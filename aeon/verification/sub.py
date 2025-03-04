from __future__ import annotations

from loguru import logger

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, TypeVar
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.verification.vcs import Conjunction, UninterpretedFunctionDeclaration
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint

ctrue = LiquidConstraint(LiquidLiteralBool(True))
cfalse = LiquidConstraint(LiquidLiteralBool(False))


def ensure_refined(t: Type) -> Type:
    """Ensures that the Base Types and TypeVars are refined. All other types remain the same."""
    match t:
        case RefinedType(_, _, _):
            return t
        case BaseType(name):
            return RefinedType(f"singleton_{name}", t, LiquidLiteralBool(True))
        case TypeVar(name):
            return RefinedType(f"singleton_tv_{name}", t,
                               LiquidLiteralBool(True))
        case _:
            return t


def is_first_order_function(at: AbstractionType):
    v: Type = at
    while isinstance(v, AbstractionType):
        match v.var_type:
            case AbstractionType(_, _, _):
                return False
            case BaseType(_) | Top() | RefinedType(_, _, _) | TypeVar(_):
                pass
            case _:
                assert False
        v = v.type
    return True


def lower_contraint_type(ttype: Type) -> Type:
    match ttype:
        case BaseType(_):
            return ttype
        case TypeVar(name):
            return BaseType(name)
        case Top():
            return BaseType("Unit")
        case AbstractionType(_, b, r):
            return AbstractionType("_", lower_contraint_type(b),
                                   lower_contraint_type(r))
        case RefinedType(_, t, _):
            return lower_contraint_type(t)
        case _:
            assert False, f"Unsupport type in constraint {ttype}"


def implication_constraint(name: str, ty: Type, c: Constraint) -> Constraint:
    match ty:
        case BaseType(_) | Top() | TypeVar(_):
            basety = lower_contraint_type(ty)
            assert isinstance(basety, BaseType)
            return Implication(name, basety, LiquidLiteralBool(True), c)
        case RefinedType(tname, ttype, tref):
            ref_subs = substitution_in_liquid(tref, LiquidVar(name), tname)
            ltype = lower_contraint_type(ttype)
            assert isinstance(ltype, BaseType) or isinstance(ltype, TypeVar)
            return Implication(name, ltype, ref_subs, c)
        case AbstractionType(_, _, _):
            # TODO Poly Refl: instead of true, reflect the implementation of the function?
            if is_first_order_function(ty):
                absty = lower_contraint_type(ty)
                assert isinstance(absty, AbstractionType)
                return UninterpretedFunctionDeclaration(name, absty, c)
            else:
                return c
        case TypePolymorphism(_, _, _):
            return c
        case _:
            assert False


def sub(t1: Type, t2: Type) -> Constraint:
    if t2 == Top():
        return ctrue
    match (ensure_refined(t1), ensure_refined(t2)):
        case RefinedType(n1, ty1, r1), RefinedType(n2, ty2, r2):
            if ty2 == Top():
                return ctrue
            if ty1 != ty2:
                return cfalse
            # Performs substition on t2 to have the same name of t1
            r2_ = substitution_in_liquid(r2, LiquidVar(n1), n2)
            rconstraint = Implication(n1, ty1, r1, LiquidConstraint(r2_))

            return rconstraint
        case TypePolymorphism(_, _, _), _:
            return ctrue
        case AbstractionType(a1, t1, r1), AbstractionType(a2, t2, r2):
            c0 = sub(t2, t1)
            r1_ = substitution_in_type(r1, Var(a2), a1)
            c1 = sub(r1_, r2)
            return Conjunction(c0, implication_constraint(a2, t2, c1))
        case _:
            logger.error(f"Failed subtyping by exhaustion: {t1} <: {t2}")
            return cfalse
