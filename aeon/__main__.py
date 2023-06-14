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
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.ctx_helpers import build_context

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="A simple argument parser")

    parser.add_argument("filename", type=str, help="name of the aeon files to be synthesized")
    parser.add_argument("--core", action="store_true", help="synthesize a aeon core file")
    parser.add_argument("-d", "--debug", action="store_true", help="debug")

    args = parser.parse_args()

    with open(args.filename) as f:
        code = f.read()

    if args.core:
        ctx = build_context(typing_vars)
        ectx = EvaluationContext(evaluation_vars)
        p = parse_term(code)
    else:
        prog: Program = parse_program(code)
        p, ctx, ectx = desugar(prog)

    if args.debug:
        print(p)

    errors = check_type_errors(ctx, p, top)
    if errors:
        print("-------------------------------")
        print("+  Type Checking Error        +")
        for error in errors:
            print("-------------------------------")
            print(error)

        print("-------------------------------")

    else:
        Synthesizer(ctx, p, top, ectx)
        # eval(p, ectx)
