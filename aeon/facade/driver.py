from dataclasses import dataclass
from functools import reduce
from typing import Any, Iterable

from aeon.synthesis.uis.api import SynthesisUI
from aeon.utils.time_utils import RecordTime
from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval
from aeon.core.types import top
from aeon.core.terms import Term
from aeon.core.bind import bind_ids
from aeon.core.substitutions import substitution
from aeon.sugar.bind import bind, bind_program
from aeon.decorators import Metadata
from aeon.frontend.anf_converter import ensure_anf
from aeon.frontend.parser import parse_term
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.desugar import DesugaredProgram, desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context, type_to_core
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import Program, STerm
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.elaboration import elaborate
from aeon.utils.ctx_helpers import build_context
from aeon.typechecking import check_type_errors
from aeon.utils.name import Name

from aeon.facade.api import AeonError


def read_file(filename: str) -> str:
    with open(filename) as file:
        return file.read()


@dataclass
class AeonConfig:
    synthesis_ui: SynthesisUI
    synthesis_budget: int
    timings: bool = False
    no_main: bool = False


class AeonDriver:
    def __init__(self, cfg: AeonConfig):
        self.cfg = cfg

    def parse_core(self, filename: str):
        # TODO: deprecate core parsing
        aeon_code = read_file(filename)
        core_typing_vars: dict[Name, Any] = reduce(
            lambda acc, el: acc | {el[0]: type_to_core(el[1], available_vars=[e for e in acc.items()])},
            typing_vars.items(),
            {},
        )

        self.typing_ctx = build_context(core_typing_vars)
        self.core_ast = parse_term(aeon_code)
        self.metadata: Metadata = {}

    def parse(self, filename: str) -> Iterable[Any]:  # TODO Type
        aeon_code = read_file(filename)

        with RecordTime("ParseSugar"):
            prog: Program = parse_main_program(aeon_code, filename=filename)
            prog = bind_program(prog, [])

        with RecordTime("Desugar"):
            desugared: DesugaredProgram = desugar(prog, is_main_hole=not self.cfg.no_main)

        with RecordTime("Bind"):
            ctx, progt = bind(desugared.elabcontext, desugared.program)
            desugared = DesugaredProgram(progt, ctx, desugared.metadata)
            metadata: Metadata = desugared.metadata

        try:
            with RecordTime("Elaboration"):
                sterm: STerm = elaborate(desugared.elabcontext, desugared.program, st_top)
        except AeonError as e:
            return [e]  # TODO: Support multiple errors

        with RecordTime("Core generation"):
            typing_ctx = lower_to_core_context(desugared.elabcontext)
            core_ast = lower_to_core(sterm)
            typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)

        with RecordTime("ANF conversion"):
            core_ast_anf = ensure_anf(core_ast)

        with RecordTime("TypeChecking"):
            type_errors = check_type_errors(typing_ctx, core_ast_anf, top)
            # TODO
            if type_errors:
                return type_errors

        with RecordTime("Preparing execution env"):
            evaluation_ctx = EvaluationContext(evaluation_vars)

        self.metadata = metadata
        self.core = core_ast_anf
        self.typing_ctx = typing_ctx
        self.evaluation_ctx = evaluation_ctx
        return []

    def run(self):
        with RecordTime("Evaluation"):
            eval(self.core, self.evaluation_ctx)

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

    def synth(self):
        with RecordTime("Synthesis"):
            synthesizer = GESynthesizer()
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
                core_ast_anf = substitution(core_ast_anf, v, k)

            self.cfg.synthesis_ui.display_results(core_ast_anf, mapping)

            # TODO: convert to sugar
            return core_ast_anf
