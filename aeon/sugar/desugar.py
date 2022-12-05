from aeon.sugar.parser import TreeToSugar
from typing import Tuple


from aeon.sugar.program import Program
from aeon.utils.ctx_helpers import build_context
from aeon.prelude.prelude import typing_vars, evaluation_vars
from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Abstraction, Application, Literal, Rec, Term, Hole, Var
from aeon.core.types import AbstractionType, t_int
from aeon.typing.context import TypeBinder, TypingContext, VariableBinder


def desugar(p: Program) -> Tuple[Term, TypingContext, EvaluationContext]:
    ctx = build_context(typing_vars)
    ectx = EvaluationContext(evaluation_vars)
    for tyname in p.type_decls:
        ctx = TypeBinder(ctx, tyname)

    if "main" in [d.name for d in p.definitions]:
        prog = Application(Var("main"), Literal(1, type=t_int))
    else:
        prog = Application(Var("print"), Hole("main"))
    for d in p.definitions[::-1]:
        if d.body == Var("uninterpreted"):
            ctx = VariableBinder(
                ctx, d.name, d.type
            )  # TODO: ensure basic type in d.type
        else:
            ty = d.type
            body = d.body
            for (a, t) in d.args:
                ty = AbstractionType(a, t, ty)
                body = Abstraction(a, body)
            prog = Rec(d.name, ty, body, prog)
    return (prog, ctx, ectx)
