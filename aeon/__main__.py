from __future__ import annotations

import argparse

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.logger.logger import export_log
from aeon.logger.logger import setup_logger
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program, Decorator
from aeon.synthesis_grammar.synthesizer import Synthesizer
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.ctx_helpers import build_context


def parse_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument("filename", help="name of the aeon files to be synthesized")
    parser.add_argument("--core", action="store_true", help="synthesize a aeon core file")
    parser.add_argument(
        "-l",
        "--log",
        nargs="+",
        default="",
        help="set log level: \nTRACE \nDEBUG \nINFO \nTYPECHECKER \nCONSTRAINT " "\nWARNINGS \nERROR \nCRITICAL",
    )
    parser.add_argument("-f", "--logfile", action="store_true", help="export log file")

    parser.add_argument("-csv", "--csv-synth", action="store_true", help="export synthesis csv file")
    return parser.parse_args()


def read_file(filename: str) -> str:
    with open(filename) as file:
        return file.read()


def process_code(
    core: bool, code: str
) -> tuple[Term, TypingContext, EvaluationContext, dict[str, tuple[Term, list[Decorator]]]]:
    if core:
        context = build_context(typing_vars)
        evaluation_ctx = EvaluationContext(evaluation_vars)
        return parse_term(code), context, evaluation_ctx, {}
    else:
        prog: Program = parse_program(code)
        return desugar(prog)


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

    aeon_code = read_file(args.filename)
    p, ctx, ectx, objectives_dict = process_code(args.core, aeon_code)
    logger.info(p)

    type_errors = check_type_errors(ctx, p, top)
    if type_errors:
        log_type_errors(type_errors)
    else:
        if objectives_dict:
            synthesizer = Synthesizer(ctx, p, top, ectx)
            file_name = args.filename if args.csv_synth else None
            best_solution = synthesizer.synthesize(
                file_name,
                objectives_dict,
            )

            print(f"Best solution: {best_solution}")
        else:
            eval(p, ectx)
