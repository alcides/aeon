import sys
import tempfile
from dataclasses import dataclass
from typing import Any, Iterable

from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval
from aeon.backend.python_export import export_function
from aeon.compilation.compile import (
    clear_unit_cache,
    compile_and_link,
    compile_and_link_program,
    dependency_units_for,
)
from aeon.compilation.link import collect_constructor_names
from aeon.core.substitutions import substitution
from aeon.core.terms import Term
from aeon.facade.api import AeonError, UndecidableRefinementError
from aeon.prelude.prelude import evaluation_vars
from aeon.sugar.bind import bind_program
from aeon.sugar.instance_registry import clear_instance_registry
from aeon.sugar.lifting import lift
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import Program, STerm
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisUI, SynthesisFormat
from aeon.typechecking.context import TypingContext
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
    # Treat refinements that leave the decidable fragment (nonlinear
    # arithmetic, ...) as errors instead of warnings (issue #438).
    strict_decidable: bool = False


class AeonDriver:
    core: Term | None
    typing_ctx: TypingContext | None

    def __init__(self, cfg: AeonConfig):
        self.cfg = cfg
        self.decidability_warnings: list = []

    def parse(self, filename: str = None, aeon_code: str = None) -> Iterable[AeonError]:
        self.core = None
        self.typing_ctx = None
        self.decidability_warnings = []

        with RecordTime("ParseSugar"):
            clear_instance_registry()
            clear_unit_cache()

        with RecordTime("Compile"):
            if aeon_code is not None:
                parse_path = filename
                if parse_path is None:
                    tmp = tempfile.NamedTemporaryFile(mode="w", suffix=".ae", delete=False, encoding="utf-8")
                    tmp.write(aeon_code)
                    tmp.close()
                    parse_path = tmp.name
                unit, core, typing_ctx, metadata, _trusted, errors = compile_and_link_program(
                    aeon_code,
                    filename=parse_path,
                    is_main=True,
                    is_main_hole=not self.cfg.no_main,
                )
            else:
                unit, core, typing_ctx, metadata, _trusted, errors = compile_and_link(
                    filename,
                    is_main=True,
                    is_main_hole=not self.cfg.no_main,
                )

        if core is not None and typing_ctx is not None:
            self.core = core
            self.typing_ctx = typing_ctx

        if errors:
            return errors
        assert core is not None and typing_ctx is not None and metadata is not None

        with RecordTime("DecidabilityScan"):
            from aeon.verification.decidability import collect_decidability_warnings

            self.decidability_warnings = collect_decidability_warnings(core, source_path=unit.source_path)
            if self.cfg.strict_decidable and self.decidability_warnings:
                return [
                    UndecidableRefinementError(construct=w.construct, detail=w.message, loc=w.location)
                    for w in self.decidability_warnings
                ]

        self.metadata = metadata

        dep_units = dependency_units_for(unit)
        self.constructor_names = collect_constructor_names(unit, dep_units)

        with RecordTime("Preparing execution env"):
            pipeline = MultiBackendPipeline(metadata=metadata)
            self.evaluation_ctx = EvaluationContext(evaluation_vars, metadata=metadata, pipeline=pipeline)

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
