from __future__ import annotations

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Abstraction
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import t_int
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.program import Definition
from aeon.sugar.program import Program
from aeon.typechecking.context import TypeBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.utils.ctx_helpers import build_context


def desugar(p: Program) -> tuple[Term, TypingContext, EvaluationContext]:
    ctx = build_context(typing_vars)
    ectx = EvaluationContext(evaluation_vars)
    for tyname in p.type_decls:
        ctx = TypeBinder(ctx, tyname)

    prog: Term
    if "main" in [d.name for d in p.definitions]:
        prog = Application(Var("main"), Literal(1, type=t_int))
    else:
        prog = Application(Var("print"), Hole("main"))
    d: Definition
    for d in p.definitions[::-1]:
        if d.body == Var("uninterpreted"):
            ctx = VariableBinder(
                ctx,
                d.name,
                d.type,
            )  # TODO: ensure basic type in d.type
        else:
            ty = d.type
            body = d.body
            for a, t in d.args:
                ty = AbstractionType(a, t, ty)
                body = Abstraction(a, body)
            prog = Rec(d.name, ty, body, prog)
    return (prog, ctx, ectx)
