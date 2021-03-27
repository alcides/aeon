import sys
from aeon.frontend.parser import parse_term, parse_type
from aeon.backend.evaluator import EvaluationContext, eval
from aeon.core.types import top
from aeon.typing.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context
from aeon.prelude.prelude import typing_vars, evaluation_vars

ctx = build_context(typing_vars)
ectx = EvaluationContext(evaluation_vars)

if __name__ == "__main__":
    fname = sys.argv[1]
    with open(fname, "r") as f:
        code = f.read()
    p = parse_term(code)
    check_type(ctx, p, top)
    eval(p, ectx)
