from aeon.sugar.parser import TreeToSugar
from typing import Tuple


from aeon.sugar.program import Program
from aeon.utils.ctx_helpers import build_context
from aeon.prelude.prelude import typing_vars, evaluation_vars
from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Abstraction, Literal, Rec, Term, Hole
from aeon.core.types import AbstractionType, t_int
from aeon.typing.context import TypeBinder, TypingContext


def desugar(p: Program) -> Tuple[Term, TypingContext, EvaluationContext]:
    ctx = build_context(typing_vars)
    ectx = EvaluationContext(evaluation_vars)
    for tyname in p.type_decls:
        ctx = TypeBinder(ctx, tyname)
    print(p)

    prog = Hole("main")
    for d in p.definitions:
        ty = d.type
        body = d.body
        for (a, t) in d.args:
            ty = AbstractionType(a, t, ty)
            body = Abstraction(a, body)
        prog = Rec(d.name, ty, body, prog)
    return (prog, ctx, ectx)
