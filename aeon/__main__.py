from __future__ import annotations

import argparse

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.synthesis_grammar.grammar import Synthesizer
from aeon.typechecking.typeinfer import check_type_errors, log_typechecker_errors, check_and_log_type_errors
from aeon.utils.ctx_helpers import build_context
from aeon.logger.logger import setup_logger

if __name__ == "__main__":

    parser = argparse.ArgumentParser()

    parser.add_argument("filename", type=str, help="name of the aeon files to be synthesized")
    parser.add_argument("--core", action="store_true", help="synthesize a aeon core file")
    parser.add_argument("-l", "--log", type=str, nargs='+', default="", help="set log level: \nTRACE \nDEBUG \nINFO "
                                                                             "\nTYPECHECKER \nCONSTRAINT \nWARNINGS "
                                                                             "\nERROR \nCRITICAL")
    parser.add_argument("-f", "--logfile", action="store_true", help="export log file")

    args = parser.parse_args()

    if args.logfile:
        logger = setup_logger(args.log, args.filename)
    else:
        logger = setup_logger(args.log)

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

    if not check_and_log_type_errors (ctx, p, top):
        Synthesizer(ctx, p, top, ectx)
        # eval(p, ectx)
