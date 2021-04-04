import sys
from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.types import top
from aeon.typing.typeinfer import check_type
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program

from aeon.utils.ctx_helpers import build_context
from aeon.prelude.prelude import typing_vars, evaluation_vars
from aeon.frontend.parser import parse_term

if __name__ == "__main__":
    fname = sys.argv[1]
    with open(fname, "r") as f:
        code = f.read()

    if "--core" in sys.argv:
        ctx = build_context(typing_vars)
        ectx = EvaluationContext(evaluation_vars)
        p = parse_term(code)
    else:
        p, ctx, ectx = desugar(parse_program(code))
    print(p)
    if check_type(ctx, p, top):
        eval(p, ectx)
    else:
        print(p, top)
        print("Type Checking failed.")
