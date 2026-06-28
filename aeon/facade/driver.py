import sys
from dataclasses import dataclass
from typing import Any, Iterable

from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval
from aeon.backend.python_export import export_function
from aeon.core.bind import bind_ids, populate_mutual_companions
from aeon.core.substitutions import substitution
from aeon.core.terms import Term
from aeon.core.types import top
from aeon.decorators import Metadata, apply_core_decorators_phase
from aeon.elaboration import elaborate_collecting_errors
from aeon.facade.api import AeonError
from aeon.prelude.prelude import evaluation_vars
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import DesugaredProgram, desugar
from aeon.sugar.instance_registry import clear_instance_registry
from aeon.sugar.lifting import lift
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import Program, STerm
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisUI, SynthesisFormat
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_node
from aeon.utils.time_utils import RecordTime
from aeon.llvm.pipeline import MultiBackendPipeline


def read_file(filename: str) -> str:
    with open(filename, encoding="utf-8") as file:
        return file.read()


@dataclass
class AeonConfig:
    synthesizer: str
    synthesis_ui: SynthesisUI
    synthesis_budget: int
    timings: bool = False
    no_main: bool = False
    synthesis_format: SynthesisFormat = SynthesisFormat.DEFAULT


class AeonDriver:
    core: Term | None
    typing_ctx: TypingContext | None

    def __init__(self, cfg: AeonConfig):
        self.cfg = cfg

    def parse(self, filename: str = None, aeon_code: str = None) -> Iterable[AeonError]:
        if aeon_code is None:
            aeon_code = read_file(filename)

        self.core = None
        self.typing_ctx = None

        return self._parse_legacy(filename, aeon_code)

    def _parse_legacy(self, filename: str | None, aeon_code: str) -> Iterable[AeonError]:
        with RecordTime("ParseSugar"):
            clear_instance_registry()
            prog: Program = parse_main_program(aeon_code, filename=filename)
            prog = bind_program(prog, [])

        with RecordTime("Desugar"):
            try:
                desugared: DesugaredProgram = desugar(prog, is_main_hole=not self.cfg.no_main)
            except AeonError as e:
                return [e]

        with RecordTime("Bind"):
            ctx, progt = bind(desugared.elabcontext, desugared.program)
            desugared = DesugaredProgram(
                progt, ctx, desugared.metadata, desugared.constructor_to_type, desugared.constructor_defs
            )
            metadata: Metadata = desugared.metadata

        with RecordTime("Elaboration"):
            sterm, elab_errors = elaborate_collecting_errors(desugared.elabcontext, desugared.program, st_top)
        if elab_errors:
            return elab_errors
        assert sterm is not None

        with RecordTime("Core generation"):
            typing_ctx = lower_to_core_context(desugared.elabcontext)
            core_ast = lower_to_core(sterm)
            typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
            core_ast = populate_mutual_companions(core_ast)

        # Expose the core program and its top-level typing context as soon as
        # they exist — before type checking — so tooling (the LSP's hover,
        # completion and type-index features) can still introspect a program
        # that elaborates but fails to type check. The later assignments on the
        # success path overwrite these with identical values.
        self.core = core_ast
        self.typing_ctx = typing_ctx

        with RecordTime("TypeChecking"):
            type_errors = check_type_errors(typing_ctx, core_ast, top)
            if type_errors:
                return type_errors

        with RecordTime("CorePhaseDecorators"):
            metadata = apply_core_decorators_phase(typing_ctx, core_ast, metadata)

        with RecordTime("Preparing execution env"):
            pipeline = MultiBackendPipeline(metadata=metadata)
            evaluation_ctx = EvaluationContext(evaluation_vars, metadata=metadata, pipeline=pipeline)

        self.metadata = metadata
        self.core = core_ast
        self.typing_ctx = typing_ctx
        self.evaluation_ctx = evaluation_ctx
        # Names (prefixed, e.g. ``List_cons``) of data constructors, so the
        # property-based tester can build constructor-only generators for ADTs.
        self.constructor_names = {n.name for n in desugared.constructor_defs.values()}

        with RecordTime("LLVM compilation"):
            pipeline.compile(self.core)

        return []

    def run(self) -> Any:
        with RecordTime("Evaluation"):
            return eval(self.core, self.evaluation_ctx)

    def trust_report(self, filename: str | None = None, for_func: str | None = None) -> str:
        """Render the program's trusted computing base — the axioms and refined
        ``native`` bindings its guarantees rest on (issue #442). Requires a
        prior successful :meth:`parse`."""
        from aeon.facade.trust import compute_trust_report, render_report

        report = compute_trust_report(self.core, filename=filename, for_func=for_func)
        return render_report(report)

    def export(self, fun_name: str) -> str:
        """Return a stand-alone, pure-Python definition of ``fun_name``.

        Synthesis runs first when the program still has holes, so an exported
        function that contains a hole is rendered with the synthesized result
        substituted in. Synthesis is silent here to keep stdout pure Python."""
        if self.has_synth():
            self._run_synthesis(SilentSynthesisUI())
        with RecordTime("Export"):
            return export_function(self.core, fun_name)

    def has_tests(self) -> bool:
        """Whether the program declares any ``@property`` functions or
        ``@example`` assertions."""
        return any(
            isinstance(entry, dict) and ("property" in entry or "examples" in entry) for entry in self.metadata.values()
        )

    def run_tests(self, seed: int = 0) -> list:
        """Check every ``@property`` function and ``@example`` assertion, print a
        pytest-style report, and return the list of failing results (empty when
        all pass)."""
        from aeon.synthesis.pbt import ExampleResult, PropertyResult, run_examples, run_properties

        results: list[PropertyResult | ExampleResult] = list(
            run_properties(
                self.typing_ctx,
                self.evaluation_ctx,
                self.core,
                self.metadata,
                seed=seed,
                constructor_names=self.constructor_names,
            )
        )
        results += run_examples(self.evaluation_ctx, self.core, self.metadata)
        for result in results:
            print(result.summary())
        failures = [r for r in results if not r.passed]
        passed = sum(1 for r in results if r.passed and r.error is None)
        print(f"\n{passed} passed, {len(failures)} failed, {len(results)} total")
        return failures

    def has_synth(self) -> bool:
        with RecordTime("DetectSynthesis"):
            self.incomplete_functions: list[
                tuple[
                    Name,
                    list[Name],
                ]
            ] = incomplete_functions_and_holes(
                self.typing_ctx,
                self.core,
            )
            return bool(self.incomplete_functions)

    def _run_synthesis(self, ui: SynthesisUI) -> dict[Name, STerm]:
        """Synthesize the open holes, substitute the results into ``self.core``
        in place, and return the per-hole solutions lifted to sugar terms."""
        synthesizer = make_synthesizer(self.cfg.synthesizer)
        mapping: dict[Name, Term] = synthesize_holes(
            self.typing_ctx,
            self.evaluation_ctx,
            self.core,
            self.incomplete_functions,
            self.metadata,
            synthesizer,
            self.cfg.synthesis_budget,
            ui,
            constructor_names=self.constructor_names,
        )

        synthesized_core: Term = self.core
        for k, v in mapping.items():
            if v is not None:
                synthesized_core = substitution(synthesized_core, v, k)
        self.core = synthesized_core

        return {k: lift(v) for k, v in mapping.items() if v is not None}

    def synth(self) -> STerm:
        with RecordTime("Synthesis"):
            sterm_mapping = self._run_synthesis(self.cfg.synthesis_ui)
            self.cfg.synthesis_ui.display_results(self.core, sterm_mapping, self.cfg.synthesis_format)
            return lift(self.core)

    def pretty_print(self, filename: str = None, should_be_fixed: bool = False) -> None:
        aeon_code = read_file(filename)
        prog: Program = parse_main_program(aeon_code, filename=filename)
        prog = bind_program(prog, [])
        pretty_prog = pretty_print_node(prog)
        print(pretty_prog)
        print()
        if should_be_fixed:
            try:
                with open(filename, "w") as f:
                    f.write(pretty_prog)
                print(f"successfully reformatted {filename}")
            except IOError as _:
                print(f"error formatting file {filename}", file=sys.stderr)
