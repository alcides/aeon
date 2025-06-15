from __future__ import annotations

from functools import reduce
import os
import sys
import argparse
from typing import Any

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
from aeon.logger.logger import export_log
from aeon.logger.logger import setup_logger
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.desugar import DesugaredProgram, desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context, type_to_core
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import Program, STerm
from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.uis.ncurses import NCursesUI
from aeon.synthesis.uis.terminal import TerminalUI
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.api import SynthesisError
from aeon.elaboration import UnificationException, elaborate
from aeon.utils.ctx_helpers import build_context
from aeon.utils.time_utils import RecordTime
from aeon.typechecking import check_type_errors
from aeon.utils.name import Name


sys.setrecursionlimit(10000)


def parse_arguments():
    parser = argparse.ArgumentParser()

    parser.add_argument("filename", help="name of the aeon files to be synthesized")
    parser.add_argument("--core", action="store_true", help="synthesize a aeon core file")
    parser.add_argument("--budget", type=int, default=60, help="Time for synthesis (in seconds).")
    parser.add_argument(
        "-l",
        "--log",
        nargs="+",
        default="",
        help="""set log level: \nTRACE \nDEBUG \nINFO \nWARNINGS \nCONSTRAINT \nTYPECHECKER \nSYNTH_TYPE \nCONSTRAINT \nSYNTHESIZER
                \nERROR \nCRITICAL\n TIME""",
    )
    parser.add_argument(
        "-f",
        "--logfile",
        action="store_true",
        help="export log file",
    )
    parser.add_argument(
        "-d",
        "--debug",
        action="store_true",
        help="Show debug information",
    )

    parser.add_argument(
        "-t",
        "--timings",
        action="store_true",
        help="Show timing information",
    )

    parser.add_argument("-n", "--no-main", action="store_true", help="Disables introducing hole in main")

    return parser.parse_args()


def read_file(filename: str) -> str:
    with open(filename) as file:
        return file.read()


def log_type_errors(errors: list[Exception | str]):
    print("TYPECHECKER", "-------------------------------")
    print("TYPECHECKER", "+     Type Checking Error     +")
    for error in errors:
        print("TYPECHECKER", "-------------------------------")
        print("TYPECHECKER", error)
    print("TYPECHECKER", "-------------------------------")


def select_synthesis_ui() -> SynthesisUI:
    if os.environ.get("TERM", None):
        return NCursesUI()
    else:
        return TerminalUI()


def main() -> None:
    args = parse_arguments()
    logger = setup_logger()
    export_log(args.log, args.logfile, args.filename)
    if args.debug:
        logger.add(sys.stderr)
    if args.timings:
        logger.add(sys.stderr, level="TIME")

    aeon_code = read_file(args.filename)

    if args.core:
        with RecordTime("ParseCore"):
            # TODO: Remove old version
            # core_typing_vars = {k: type_to_core(typing_vars[k]) for k in typing_vars}

            core_typing_vars: dict[Name, Any] = reduce(
                lambda acc, el: acc | {el[0]: type_to_core(el[1], available_vars=[e for e in acc.items()])},
                typing_vars.items(),
                {},
            )

            typing_ctx = build_context(core_typing_vars)
            core_ast = parse_term(aeon_code)
            metadata: Metadata = {}
    else:
        with RecordTime("ParseSugar"):
            prog: Program = parse_main_program(aeon_code, filename=args.filename)
            prog = bind_program(prog, [])

        with RecordTime("Desugar"):
            desugared: DesugaredProgram = desugar(prog, is_main_hole=not args.no_main)

        with RecordTime("Bind"):
            ctx, progt = bind(desugared.elabcontext, desugared.program)
            desugared = DesugaredProgram(progt, ctx, desugared.metadata)
            metadata = desugared.metadata

        try:
            with RecordTime("Elaboration"):
                sterm: STerm = elaborate(desugared.elabcontext, desugared.program, st_top)
        except UnificationException as e:
            log_type_errors([e])
            sys.exit(1)

        with RecordTime("Core generation"):
            typing_ctx = lower_to_core_context(desugared.elabcontext)
            core_ast = lower_to_core(sterm)
            typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
            logger.debug(core_ast)

    with RecordTime("ANF conversion"):
        core_ast_anf = ensure_anf(core_ast)
        logger.debug(core_ast_anf)

    with RecordTime("TypeChecking"):
        type_errors = check_type_errors(typing_ctx, core_ast_anf, top)
    if type_errors:
        log_type_errors(type_errors)
        sys.exit(1)

    with RecordTime("Preparing execution env"):
        evaluation_ctx = EvaluationContext(evaluation_vars)

    with RecordTime("DetectSynthesis"):
        incomplete_functions: list[
            tuple[
                Name,
                list[Name],
            ]
        ] = incomplete_functions_and_holes(
            typing_ctx,
            core_ast_anf,
        )

    if incomplete_functions:
        ui = select_synthesis_ui()

        with RecordTime("Synthesis"):
            try:
                synthesizer = GESynthesizer()
                mapping: dict[Name, Term] = synthesize_holes(
                    typing_ctx,
                    evaluation_ctx,
                    core_ast_anf,
                    incomplete_functions,
                    metadata,
                    synthesizer,
                    args.budget,
                    ui,
                )

                for k, v in mapping.items():
                    core_ast_anf = substitution(core_ast_anf, v, k)

                ui.display_results(core_ast_anf, mapping)
            except SynthesisError as e:
                print("SYNTHESIZER", "-------------------------------")
                print("SYNTHESIZER", "+     Synthesis Error     +")
                print("SYNTHESIZER", e)
                print("SYNTHESIZER", "-------------------------------")
                sys.exit(1)
        sys.exit(0)
    with RecordTime("Evaluation"):
        eval(core_ast_anf, evaluation_ctx)


if __name__ == "__main__":
    main()
