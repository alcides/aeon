from __future__ import annotations

from loguru import logger

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, TypeConstructor, TypeVar
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism, RefinimentPolymorphism
from aeon.core.types import t_unit
from aeon.typechecking.context import TypingContext
from aeon.verification.vcs import Conjunction, UninterpretedFunctionDeclaration
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.utils.name import Name, fresh_counter

ctrue = LiquidConstraint(LiquidLiteralBool(True))
cfalse = LiquidConstraint(LiquidLiteralBool(False))


def ensure_refined(t: Type) -> Type:
    """Ensures that the Base Types and TypeVars are refined. All other types remain the same."""
    match t:
        case RefinedType(_, _, _):
            return t
        case TypeVar(Name(name)):
            return RefinedType(Name(f"singleton_{name}", fresh_counter.fresh()), t, LiquidLiteralBool(True))
        case TypeConstructor(Name(name), _):
            return RefinedType(Name(f"singleton_{name}", fresh_counter.fresh()), t, LiquidLiteralBool(True))
        case _:
            return t


def is_first_order_function(at: AbstractionType):
    v: Type = at
    while isinstance(v, AbstractionType):
        match v.var_type:
            case AbstractionType(_, _, _):
                return False
            case Top() | RefinedType(_, _, _) | TypeVar(_) | TypeConstructor(_, _):
                pass
            case _:
                assert False
        v = v.type
    return True


def lower_constraint_type(ttype: Type) -> Type:
    match ttype:
        case TypeVar(name):
            return TypeConstructor(name)
        case Top():
            return t_unit
        case AbstractionType(name, b, r):
            return AbstractionType(name, lower_constraint_type(b), lower_constraint_type(r))
        case RefinedType(_, t, _):
            return lower_constraint_type(t)
        case TypeConstructor(name, args):
            if args:
                # Polymorphic types are represented by top
                return TypeConstructor(Name("Top", 0))
            else:
                return TypeConstructor(name)

        case _:
            assert False, f"Unsupport type in constraint {ttype} ({type(ttype)})"


def implication_constraint(name: Name, ty: Type, c: Constraint) -> Constraint:
    match ty:
        case Top() | TypeVar(_) | TypeConstructor(_, _):
            basety = lower_constraint_type(ty)
            assert isinstance(basety, TypeConstructor)
            return Implication(name, basety, LiquidLiteralBool(True), c)
        case RefinedType(tname, ttype, tref):
            ref_subs = substitution_in_liquid(tref, LiquidVar(name), tname)
            ltype = lower_constraint_type(ttype)
            assert isinstance(ltype, TypeConstructor) or isinstance(ltype, TypeVar)
            return Implication(name, ltype, ref_subs, c)
        case AbstractionType(_, _, _):
            # TODO Poly Refl: instead of true, reflect the implementation of the function?
            if is_first_order_function(ty):
                absty = lower_constraint_type(ty)
                assert isinstance(absty, AbstractionType)
                return UninterpretedFunctionDeclaration(name, absty, c)
            else:
                return c
        case TypePolymorphism(_, _, _):
            return c
        case RefinimentPolymorphism(_, _, _):
            return c
        case _:
            assert False


def sub(ctx: TypingContext, t1: Type, t2: Type) -> Constraint:
    if t2 == Top():
        return ctrue
    match (ensure_refined(t1), ensure_refined(t2)):
        case RefinedType(n1, ty1, r1), RefinedType(n2, ty2, r2):
            if ty2 == Top():
                return ctrue
            if ty1 != ty2:
                return cfalse

            new_name: Name = Name(n1.name + n2.name, fresh_counter.fresh())

            # Performs substition on t2 to have the same name of t1
            r2_ = substitution_in_liquid(r2, LiquidVar(new_name), n2)
            r1_ = substitution_in_liquid(r1, LiquidVar(new_name), n1)
            lowert = lower_constraint_type(ty1)
            assert isinstance(lowert, TypeConstructor)
            rconstraint = Implication(new_name, lowert, r1_, LiquidConstraint(r2_))

            return rconstraint
        case TypePolymorphism(_, _, _), _:
            return ctrue
        case RefinimentPolymorphism(_, _, _), _:
            return ctrue
        case AbstractionType(a1, t1, rt1), AbstractionType(a2, t2, rt2):
            new_name_a: Name = Name(a1.name + a2.name, fresh_counter.fresh())

            c0 = sub(ctx, t2, t1)
            rt1_ = substitution_in_type(rt1, Var(new_name_a), a1)
            rt2_ = substitution_in_type(rt2, Var(new_name_a), a2)
            c1 = sub(ctx, rt1_, rt2_)
            return Conjunction(c0, implication_constraint(new_name_a, t2, c1))
        case TypeConstructor(name1, args1), TypeConstructor(name2, args2):
            if name1 != name2:
                return cfalse
            if len(args1) != len(args2):
                return cfalse
            for it1, it2 in zip(args1, args2):
                if it1 != it2:  # TODO polytypes: subtyping here?
                    return cfalse
            return ctrue
        case _:
            logger.error(f"Failed subtyping by exhaustion: {t1} <: {t2}")
            return cfalse
