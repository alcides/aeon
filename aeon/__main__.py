from __future__ import annotations

import os
import sys

import argparse

from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval
from aeon.core.types import top
from aeon.decorators import Metadata
from aeon.frontend.anf_converter import ensure_anf
from aeon.frontend.parser import parse_term
from aeon.logger.logger import export_log
from aeon.logger.logger import setup_logger
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.synthesis.api import SilentSynthesisUI, SynthesisUI
from aeon.synthesis.uis.ncurses import NCursesUI
from aeon.synthesis_grammar.identification import incomplete_functions_and_holes
from aeon.synthesis_grammar.synthesizer import synthesize, parse_config
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.ctx_helpers import build_context
from aeon.utils.time_utils import RecordTime


def parse_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "filename",
        help="name of the aeon files to be synthesized",
    )
    parser.add_argument(
        "--core",
        action="store_true",
        help="synthesize a aeon core file",
    )
    parser.add_argument(
        "-l",
        "--log",
        nargs="+",
        default="",
        help=
        """set log level: \nTRACE \nDEBUG \nINFO \nWARNINGS \nTYPECHECKER \nSYNTH_TYPE \nCONSTRAINT \nSYNTHESIZER
                \nERROR \nCRITICAL\n TIME""",
    )
    parser.add_argument("-f",
                        "--logfile",
                        action="store_true",
                        help="export log file")

    parser.add_argument("-csv",
                        "--csv-synth",
                        action="store_true",
                        help="export synthesis csv file")

    parser.add_argument("-gp",
                        "--gp-config",
                        help="path to the GP configuration file")

    parser.add_argument("-csec",
                        "--config-section",
                        help="section name in the GP configuration file")

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

    parser.add_argument(
        "-rg",
        "--refined-grammar",
        action="store_true",
        help="Use the refined grammar for synthesis",
    )
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
            typing_ctx = build_context(typing_vars)
            evaluation_ctx = EvaluationContext(evaluation_vars)
            core_ast = parse_term(aeon_code)
            metadata: Metadata = {}
    else:
        with RecordTime("ParseSugar"):
            prog: Program = parse_program(aeon_code)

        with RecordTime("DeSugar"):
            (
                core_ast,
                typing_ctx,
                evaluation_ctx,
                metadata,
            ) = desugar(prog)

    logger.debug(core_ast)

    with RecordTime("ANF conversion"):
        core_ast_anf = ensure_anf(core_ast)
        logger.debug(core_ast)

    with RecordTime("TypeChecking"):
        type_errors = check_type_errors(typing_ctx, core_ast_anf, top)
    if type_errors:
        log_type_errors(type_errors)
        sys.exit(1)

    with RecordTime("DetectSynthesis"):
        incomplete_functions: list[tuple[
            str, list[str]]] = incomplete_functions_and_holes(
                typing_ctx, core_ast_anf)

    if incomplete_functions:
        filename = args.filename if args.csv_synth else None
        with RecordTime("ParseConfig"):
            synth_config = (parse_config(args.gp_config, args.config_section)
                            if args.gp_config and args.config_section else
                            None)

        ui: SynthesisUI
        if os.environ.get("TERM", None):
            ui = NCursesUI()
        else:
            ui = SilentSynthesisUI()

        with RecordTime("Synthesis"):
            _, terms = synthesize(
                typing_ctx,
                evaluation_ctx,
                core_ast_anf,
                incomplete_functions,
                metadata,
                filename,
                synth_config,
                args.refined_grammar,
                ui,
            )
            print("Synthesized holes:")
            for name in terms:
                print(f"?{name}: {terms[name]}")
            # print()
            # pretty_print_term(ensure_anf(synthesis_result, 200))
        sys.exit(0)
    with RecordTime("Evaluation"):
        eval(core_ast, evaluation_ctx)


if __name__ == "__main__":
    main()
