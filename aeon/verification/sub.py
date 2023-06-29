from __future__ import annotations

from loguru import logger

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, TypeVar
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint

ctrue = LiquidConstraint(LiquidLiteralBool(True))
cfalse = LiquidConstraint(LiquidLiteralBool(False))


def ensure_refined(t: Type) -> RefinedType:
    if isinstance(t, RefinedType):
        return t
    elif isinstance(t, BaseType):
        return RefinedType(f"singleton_{t}", t, LiquidLiteralBool(True))
    assert False


def implication_constraint(name: str, t: Type, c: Constraint) -> Constraint:
    if isinstance(t, RefinedType):
        ref_subs = substitution_in_liquid(t.refinement, LiquidVar(name), t.name)
        assert isinstance(t.type, BaseType)
        return Implication(name, t.type, ref_subs, c)
    elif isinstance(t, BaseType):
        return Implication(name, t, LiquidLiteralBool(True), c)
    elif isinstance(t, AbstractionType):
        return implication_constraint(
            t.var_name,
            t.var_type,
            implication_constraint(name, t.type, c),
        )  # TODO: email Rahjit
    elif isinstance(t, TypeVar):
        # TODO: We are using Int here, but it could have been a singleton.
        return Implication(name, BaseType("Int"), LiquidLiteralBool(True), c)
    elif isinstance(t, Bottom):
        return c
    elif isinstance(t, Top):
        return c
    logger.debug(f"{name} : {t} => {c} ({type(t)})")
    assert False


def sub(t1: Type, t2: Type) -> Constraint:
    if isinstance(t2, Top) or isinstance(t1, Bottom):
        return ctrue
    if isinstance(t1, BaseType):
        t1 = ensure_refined(t1)
    if isinstance(t2, BaseType):
        t2 = ensure_refined(t2)
    if isinstance(t1, RefinedType) and isinstance(t2, RefinedType):
        if isinstance(t1.type, Bottom) or isinstance(t2.type, Top):
            return ctrue
        elif t1.type == t2.type:
            t2_subs = substitution_in_liquid(t2.refinement, LiquidVar(t1.name), t2.name)
            assert isinstance(t1.type, BaseType)  # TODO: check this
            return Implication(
                t1.name,
                t1.type,
                t1.refinement,
                LiquidConstraint(t2_subs),
            )
        else:
            return cfalse
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        c0 = sub(t2.var_type, t1.var_type)
        c1 = sub(substitution_in_type(t1.type, Var(t2.var_name), t1.var_name), t2.type)
        return Conjunction(c0, implication_constraint(t2.var_name, t2.var_type, c1))
    else:
        return cfalse
