import sys
from dataclasses import dataclass
from typing import Any, Iterable

from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval
from aeon.core.bind import bind_ids
from aeon.core.substitutions import substitution
from aeon.core.terms import Term
from aeon.core.types import top
from aeon.decorators import Metadata, apply_core_decorators_phase
from aeon.elaboration import elaborate
from aeon.facade.api import AeonError
from aeon.frontend.anf_converter import ensure_anf
from aeon.prelude.prelude import evaluation_vars
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.bind import bind, bind_program
from aeon.sugar.desugar import DesugaredProgram, desugar
from aeon.sugar.lifting import lift
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import Program, STerm
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SynthesisUI, SynthesisFormat
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
    skip_elaboration: bool = False


class AeonDriver:
    def __init__(self, cfg: AeonConfig):
        self.cfg = cfg

    def parse(self, filename: str = None, aeon_code: str = None) -> Iterable[AeonError]:
        if aeon_code is None:
            aeon_code = read_file(filename)

        with RecordTime("ParseSugar"):
            prog: Program = parse_main_program(aeon_code, filename=filename)
            prog = bind_program(prog, [])

        with RecordTime("Desugar"):
            try:
                desugared: DesugaredProgram = desugar(prog, is_main_hole=not self.cfg.no_main)
            except AeonError as e:
                return [e]

        with RecordTime("Bind"):
            ctx, progt = bind(desugared.elabcontext, desugared.program)
            desugared = DesugaredProgram(progt, ctx, desugared.metadata)
            metadata: Metadata = desugared.metadata

        try:
            if self.cfg.skip_elaboration:
                sterm: STerm = desugared.program
            else:
                with RecordTime("Elaboration"):
                    sterm = elaborate(desugared.elabcontext, desugared.program, st_top)
        except AeonError as e:
            return [e]  # TODO: Support multiple errors

        with RecordTime("Core generation"):
            typing_ctx = lower_to_core_context(desugared.elabcontext)
            core_ast = lower_to_core(sterm)
            typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)

        with RecordTime("ANF conversion"):
            core_ast_anf = ensure_anf(core_ast)

        if not self.cfg.skip_elaboration:
            with RecordTime("TypeChecking"):
                type_errors = check_type_errors(typing_ctx, core_ast_anf, top)
                # TODO
                if type_errors:
                    return type_errors

        with RecordTime("CorePhaseDecorators"):
            metadata = apply_core_decorators_phase(typing_ctx, core_ast_anf, metadata)

        with RecordTime("Preparing execution env"):
            pipeline = MultiBackendPipeline(metadata=metadata)
            evaluation_ctx = EvaluationContext(evaluation_vars, metadata=metadata, pipeline=pipeline)

        self.metadata = metadata
        self.core = core_ast_anf
        self.typing_ctx = typing_ctx
        self.evaluation_ctx = evaluation_ctx

        with RecordTime("LLVM compilation"):
            pipeline.compile(self.core)

        return []

    def run(self) -> Any:
        with RecordTime("Evaluation"):
            return eval(self.core, self.evaluation_ctx)

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

    def synth(self) -> STerm:
        with RecordTime("Synthesis"):
            synthesizer = make_synthesizer(self.cfg.synthesizer)
            mapping: dict[Name, Term] = synthesize_holes(
                self.typing_ctx,
                self.evaluation_ctx,
                self.core,
                self.incomplete_functions,
                self.metadata,
                synthesizer,
                self.cfg.synthesis_budget,
                self.cfg.synthesis_ui,
            )

            core_ast_anf: Term = self.core
            for k, v in mapping.items():
                if v is not None:
                    core_ast_anf = substitution(core_ast_anf, v, k)

            sterm_mapping: dict[Name, STerm] = {k: lift(v) for k, v in mapping.items() if v is not None}

            self.cfg.synthesis_ui.display_results(core_ast_anf, sterm_mapping, self.cfg.synthesis_format)

            return lift(core_ast_anf)

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
