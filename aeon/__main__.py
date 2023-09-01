from __future__ import annotations

import argparse

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.logger.logger import setup_logger
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.ctx_helpers import build_context

if __name__ == "__main__":

    parser = argparse.ArgumentParser()

    parser.add_argument("filename", type=str, help="name of the aeon files to be synthesized")
    parser.add_argument("--core", action="store_true", help="synthesize a aeon core file")
    parser.add_argument("-l", "--log", type=str, nargs='+', default="", help="set log level")
    parser.add_argument("-f", "--logfile", action="store_true", help="export log file")

    args = parser.parse_args()

    logger = setup_logger(args.log, args.filename) if args.logfile else setup_logger(args.log)

    with open(args.filename) as f:
        code = f.read()

    if args.core:
        ctx = build_context(typing_vars)
        ectx = EvaluationContext(evaluation_vars)
        p = parse_term(code)
    else:
        prog: Program = parse_program(code)
        p, ctx, ectx = desugar(prog)

    logger.info(p)

    errors = check_type_errors(ctx, p, top)
    if errors:
        logger.log("TYPECHECKER", "-------------------------------")
        logger.log("TYPECHECKER", "+  Type Checking Error        +")
        for error in errors:
            logger.log("TYPECHECKER", "-------------------------------")
            logger.log("TYPECHECKER", error)

        logger.log("TYPECHECKER", "-------------------------------")

    else:
        eval(p, ectx)
