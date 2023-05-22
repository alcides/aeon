from __future__ import annotations

import sys

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.synthesis_grammar.grammar import synthesis
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.ctx_helpers import build_context

if __name__ == "__main__":
    fname = sys.argv[1]
    with open(fname) as f:
        code = f.read()

    if "--core" in sys.argv:
        ctx = build_context(typing_vars)
        ectx = EvaluationContext(evaluation_vars)
        p = parse_term(code)
    else:
        prog: Program = parse_program(code)
        p, ctx, ectx = desugar(prog)
    if "-d" in sys.argv or "--debug" in sys.argv:
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
        synthesis(ctx, p, top, ectx)
        eval(p, ectx)
