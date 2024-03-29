from __future__ import annotations

import sys
import time

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
from aeon.synthesis_grammar.identification import incomplete_functions_and_holes
from aeon.synthesis_grammar.synthesizer import synthesize, parse_config
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.ctx_helpers import build_context


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
        help="""set log level: \nTRACE \nDEBUG \nINFO \nWARNINGS \nTYPECHECKER \nSYNTH_TYPE \nCONSTRAINT \nSYNTHESIZER
                \nERROR \nCRITICAL""",
    )
    parser.add_argument("-f", "--logfile", action="store_true", help="export log file")

    parser.add_argument("-csv", "--csv-synth", action="store_true", help="export synthesis csv file")

    parser.add_argument("-gp", "--gp-config", help="path to the GP configuration file")

    parser.add_argument("-csec", "--config-section", help="section name in the GP configuration file")

    parser.add_argument(
        "-d",
        "--debug",
        action="store_true",
        help="Show debug information",
    )
    return parser.parse_args()


def read_file(filename: str) -> str:
    with open(filename) as file:
        return file.read()


def log_type_errors(errors: list[Exception | str]):
    logger.log("TYPECHECKER", "-------------------------------")
    logger.log("TYPECHECKER", "+     Type Checking Error     +")
    for error in errors:
        logger.log("TYPECHECKER", "-------------------------------")
        logger.log("TYPECHECKER", error)
    logger.log("TYPECHECKER", "-------------------------------")


if __name__ == "__main__":
    args = parse_arguments()
    logger = setup_logger()
    export_log(args.log, args.logfile, args.filename)
    if args.debug:
        logger.add(sys.stderr)

    aeon_code = read_file(args.filename)

    if args.core:
        typing_ctx = build_context(typing_vars)
        evaluation_ctx = EvaluationContext(evaluation_vars)
        core_ast = parse_term(aeon_code)
        metadata: Metadata = {}
    else:
        start = time.time()
        prog: Program = parse_program(aeon_code)
        end = time.time()
        logger.info(f"Parsing time: {end - start}")
        start = time.time()
        (
            core_ast,
            typing_ctx,
            evaluation_ctx,
            metadata,
        ) = desugar(prog)
        end = time.time()
        logger.info(f"Desugaring time: {end - start} seconds")
    logger.info(core_ast)
    start = time.time()
    core_ast_anf = ensure_anf(core_ast)
    print(core_ast_anf)
    end = time.time()
    logger.info(f"ANF conversion time: {end - start} seconds")

    start = time.time()
    type_errors = check_type_errors(typing_ctx, core_ast_anf, top)
    end = time.time()
    logger.info(f"Type checking time: {end - start} seconds")
    if type_errors:
        log_type_errors(type_errors)
        sys.exit(1)

    start = time.time()
    incomplete_functions: list[tuple[str, list[str]]] = incomplete_functions_and_holes(typing_ctx, core_ast_anf)
    end = time.time()
    logger.info(f"Incomplete Functions identification time: {end - start} seconds")

    if incomplete_functions:
        filename = args.filename if args.csv_synth else None
        start = time.time()
        synth_config = (
            parse_config(args.gp_config, args.config_section) if args.gp_config and args.config_section else None
        )
        end = time.time()
        logger.info(f"Config parsing time: {end - start} seconds")

        synthesis_result = synthesize(
            typing_ctx,
            evaluation_ctx,
            core_ast_anf,
            incomplete_functions,
            metadata,
            filename,
            synth_config,
        )
        print(f"Best solution:{synthesis_result}")
        # print()
        # pretty_print_term(ensure_anf(synthesis_result, 200))
        sys.exit(1)
    start = time.time()
    eval(core_ast, evaluation_ctx)
    end = time.time()
    logger.info(f"Evaluation time: {end - start} seconds")
