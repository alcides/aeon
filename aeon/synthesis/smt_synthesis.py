from __future__ import annotations

import z3

from aeon.core.liquid import LiquidTerm
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import extract_parts
from aeon.core.types import RefinedType
from aeon.core.types import t_int
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypeBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.verification.smt import make_variable
from aeon.verification.smt import translate_liq


def translate(ctx: TypingContext, t: LiquidTerm, vars=[]):
    if isinstance(ctx, EmptyContext):
        return translate_liq(t, variables=vars)
    elif isinstance(ctx, VariableBinder):
        if isinstance(ctx.type, RefinedType) or isinstance(ctx.type, BaseType):
            (name, base, cond) = extract_parts(ctx.type)

            assert isinstance(base, BaseType)
            v = make_variable(name, base)
            nvars = vars + [(name, v)]

            req = translate_liq(cond, variables=nvars)
            inner = translate(ctx.prev, t, nvars)
            return z3.ForAll([v], z3.Implies(req, inner))

        elif isinstance(ctx.type, AbstractionType):
            return translate(ctx.prev, t, vars)
        else:
            print("ERROR HERE", ctx.type, type(ctx.type))

        return translate(ctx.prev, t, vars)

    elif isinstance(ctx, TypeBinder):
        return translate(ctx.prev, t)


def smt_synth_int_lit(ctx: TypingContext, t: RefinedType, seed: int) -> int | None:
    assert t.type == t_int
    s = z3.Solver()
    s.set(":random-seed", seed)
    assert isinstance(t.type, BaseType)  # TODO: check this assert
    v = make_variable(t.name, t.type)
    expr = translate(ctx, t.refinement, vars=[(t.name, v)])
    s.add(expr)
    if s.check():
        if len(s.model()):
            litv = s.model()[v]
            return int(str(litv))
        else:
            # This is the case where the model has no variables
            return seed
    else:
        print("No")
        return None
