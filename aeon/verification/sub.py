from __future__ import annotations


from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, ExistentialType, TypeVar
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
    elif isinstance(t, BaseType) or isinstance(t, Top) or isinstance(t, Bottom) or isinstance(t, TypeVar):
        return RefinedType(f"singleton_{t}", t, LiquidLiteralBool(True))
    assert False


def implication_constraint(name: str, t: Type, c: Constraint) -> Constraint:
    match t:
        case Bottom():
            return c
        case Top():
            return c
        case BaseType(name=_):
            return Implication(name, t, LiquidLiteralBool(True), c)
        case RefinedType(name=rname, type=ty, refinement=refinement):
            ref_subs = substitution_in_liquid(refinement, LiquidVar(name), rname)
            return Implication(name, ty, ref_subs, c)
        case AbstractionType(var_name=var_name, var_type=var_type, type=ty):
            return implication_constraint(
                var_name,  # TODO: Double-check if this needs to be a base type!
                var_type,
                implication_constraint(name, ty, c),
            )
        case TypeVar(name=_):
            # TODO: We should create a custom sort instead of Int.
            return Implication(name, BaseType("Int"), LiquidLiteralBool(True), c)
        case ExistentialType(var_name=var_name, var_type=var_type, type=ty):
            return implication_constraint(var_name, var_type, implication_constraint(name, ty, c))
        case _:
            print(f"{name} : {t} => {c} ({type(t)})")
            assert False


def ensure_safe_type(t: Type) -> BaseType:
    if isinstance(t, Top) or isinstance(t, Bottom):
        return BaseType("Bool")
    elif isinstance(t, BaseType):
        return t
    print(f"Unsafe: {t}")
    assert False


def sub(t1: Type, t2: Type) -> Constraint:
    if isinstance(t2, Top) or isinstance(t1, Bottom):
        return ctrue
    if isinstance(t1, BaseType):
        t1 = ensure_refined(t1)
    if isinstance(t2, BaseType):
        t2 = ensure_refined(t2)
    if isinstance(t2, ExistentialType):
        assert False
    if isinstance(t1, ExistentialType):
        c = sub(t1.type, t2)
        return implication_constraint(t1.var_name, t1.var_type, c)
    elif isinstance(t1, RefinedType) and isinstance(t2, RefinedType):
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
