from __future__ import annotations

from loguru import logger

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, TypeConstructor, TypeVar
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.typechecking.context import Polarity, TypingContext
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
    elif isinstance(t, TypeVar):
        return RefinedType(f"singleton_tv_{t}", t, LiquidLiteralBool(True))
    elif isinstance(t, TypeConstructor):
        return RefinedType(f"singleton_tv_{t}", t, LiquidLiteralBool(True))
    assert False


def is_first_order_function(at: AbstractionType):
    v: Type = at
    while isinstance(v, AbstractionType):
        match v.var_type:
            case AbstractionType(_, _, _):
                return False
            case BaseType(_) | Top() | Bottom() | RefinedType(_, _, _):
                pass
            case _:
                assert False
        v = v.type
    return True


def implication_constraint(name: str, ty: Type, c: Constraint) -> Constraint:
    match ty:
        case BaseType(_) | Bottom() | Top():
            return Implication(name, ty, LiquidLiteralBool(True), c)
        case RefinedType(tname, ttype, tref):
            ref_subs = substitution_in_liquid(tref, LiquidVar(name), tname)
            match ttype:
                case TypeVar(_):
                    t_ = BaseType("TypeVarPlaceHolder")
                case TypeConstructor(_):
                    t_ = BaseType("TypeConstructorPlaceHolder")
                case _:
                    t_ = ttype
            assert isinstance(t_, BaseType) or isinstance(t_, Top) or isinstance(t_, Bottom)
            return Implication(name, t_, ref_subs, c)
        case AbstractionType(_, _, _):
            # TODO Poly Refl: instead of true, reflect the implementation of the function?
            if is_first_order_function(ty):
                return Implication(name, ty, LiquidLiteralBool(True), c)
            else:
                return c
        case TypeVar(_):
            # TODO Sorts: We are using Int here, but it could have been a singleton.
            return implication_constraint(name, BaseType("TypeVarPlaceHolder"), c)
        case TypePolymorphism(_, _, _):
            return c
        case TypeConstructor(name, _):
            return implication_constraint(name, BaseType("TypeConstructorPlaceHolder"), c)
            # TODO: Double check this. Instead of a new BaseType, we should use typeclasses/nominal subclasses.
        case _:
            assert False


def sub(ctx: TypingContext, t1: Type, t2: Type) -> Constraint:
    if isinstance(t2, Top) or isinstance(t1, Bottom):
        return ctrue
    if isinstance(t1, BaseType) or isinstance(t1, TypeVar) or isinstance(t1, TypeConstructor):
        t1 = ensure_refined(t1)
    if isinstance(t2, BaseType) or isinstance(t1, TypeVar) or isinstance(t2, TypeConstructor):
        t2 = ensure_refined(t2)

    base_condition: Constraint = ctrue
    if isinstance(t1, RefinedType) and isinstance(t2, RefinedType):
        if isinstance(t1.type, Bottom) or isinstance(t2.type, Top):
            return ctrue
        elif isinstance(t1.type, BaseType) and isinstance(t2.type, BaseType):
            if t1.type.name != t2.type.name:
                return cfalse
            base_type = t1.type
        elif isinstance(t1.type, TypeVar) and isinstance(t2.type, TypeVar):
            if t1.type.name != t2.type.name:
                return cfalse
            base_type = BaseType("TypeVarPlaceHolder")
        elif isinstance(t1.type, TypeConstructor) and isinstance(t2.type, TypeConstructor):
            if t1.type.name != t2.type.name:
                return cfalse
            typed_parameters = ctx.type_constructor_named(t1.type.name)
            if not typed_parameters:
                logger.error(f"Could not subtype: {t1} <: {t2} because type constructors do not match.")
                return cfalse

            for it1, it2, (name, kind, polarity) in zip(t1.type.args, t2.type.args, typed_parameters):
                match polarity:
                    case Polarity.NEITHER:
                        pass
                    case Polarity.POSITIVE:
                        base_condition = Conjunction(base_condition, sub(ctx, it1, it2))
                    case Polarity.NEGATIVE:
                        base_condition = Conjunction(base_condition, sub(ctx, it2, it1))
                    case Polarity.BOTH:
                        base_condition = Conjunction(base_condition, sub(ctx, it1, it2))
                        base_condition = Conjunction(base_condition, sub(ctx, it2, it1))
            base_type = BaseType("TypeConstructorPlaceHolder")
        else:
            logger.error(f"Could not subtype: {t1} <: {t2} because of non-refined type.")
            return cfalse
        assert isinstance(base_type, BaseType)

        t2_subs = substitution_in_liquid(
            t2.refinement,
            LiquidVar(t1.name),
            t2.name,
        )

        return Conjunction(
            base_condition,
            Implication(
                t1.name,
                base_type,
                t1.refinement,
                LiquidConstraint(t2_subs),
            ),
        )
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        c0 = sub(ctx, t2.var_type, t1.var_type)
        c1 = sub(
            ctx,
            substitution_in_type(t1.type, Var(t2.var_name), t1.var_name),
            t2.type,
        )
        return Conjunction(
            c0,
            implication_constraint(t2.var_name, t2.var_type, c1),
        )
    elif (
        isinstance(t1, TypeVar)
        and isinstance(
            t2,
            TypeVar,
        )
        and t1.name == t2.name
    ):
        return ctrue
    else:
        logger.error(f"Failed subtyping by exhaustion: {t1} <: {t2}")
        return cfalse
