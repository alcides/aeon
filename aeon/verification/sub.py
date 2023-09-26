from __future__ import annotations

from loguru import logger

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, TypeConstructor
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
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


def implication_constraint(name: str, t: Type, c: Constraint) -> Constraint:
    if isinstance(t, RefinedType):
        ref_subs = substitution_in_liquid(t.refinement, LiquidVar(name),
                                          t.name)
        if isinstance(t.type, TypeVar):
            t_ = BaseType("TypeVarPlaceHolder")  # TODO: Rethink this
        elif isinstance(t.type, TypeConstructor):
            t_ = BaseType("TypeConstructorPlaceHolder")  # TODO: Rethink this
        else:
            t_ = t.type
        assert isinstance(t_, BaseType)
        return Implication(name, t_, ref_subs, c)
    elif isinstance(t, BaseType):
        return Implication(name, t, LiquidLiteralBool(True), c)
    elif isinstance(t, AbstractionType):
        return implication_constraint(
            t.var_name,
            t.var_type,
            implication_constraint(name, t.type, c),
        )  # TODO: email Rahjit
        """
        TODO: email Rahjit

        The rec_scope test fails.
        A refined type in a Rec escapes to the remaining of the program.

        """
    elif isinstance(t, Bottom):
        return c
    elif isinstance(t, Top):
        return c
    elif isinstance(t, TypeVar):
        return implication_constraint(name, BaseType("TypeVarPlaceHolder"), c)
    elif isinstance(t, TypeConstructor):
        return implication_constraint(name,
                                      BaseType("TypeConstructorPlaceHolder"),
                                      c)
        # TODO: Double check this. Instead of Integer, we should use typeclasses/nominal subclasses.
    elif isinstance(t, TypePolymorphism):
        return implication_constraint(t.name, t.body, c)
    assert False


def sub(t1: Type, t2: Type) -> Constraint:
    if isinstance(t2, Top) or isinstance(t1, Bottom):
        return ctrue
    if isinstance(t1, BaseType) or isinstance(t1, TypeVar) or isinstance(
            t1, TypeConstructor):
        t1 = ensure_refined(t1)
    if isinstance(t2, BaseType) or isinstance(t1, TypeVar) or isinstance(
            t2, TypeConstructor):
        t2 = ensure_refined(t2)
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
        elif isinstance(t1.type, TypeConstructor) and isinstance(
                t2.type, TypeConstructor):
            if t1.type.name != t2.type.name:
                return cfalse
            for it1, it2 in zip(t1.type.args, t2.type.args):
                if it1 != it2:
                    return cfalse
            base_type = BaseType("TypeConstructorPlaceHolder")
        else:
            logger.error(
                f"Could not subtype: {t1} <: {t2} because of non-refined type."
            )
            return cfalse
        assert isinstance(base_type, BaseType)

        t2_subs = substitution_in_liquid(
            t2.refinement,
            LiquidVar(t1.name),
            t2.name,
        )
        return Implication(
            t1.name,
            base_type,
            t1.refinement,
            LiquidConstraint(t2_subs),
        )
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        c0 = sub(t2.var_type, t1.var_type)
        c1 = sub(
            substitution_in_type(t1.type, Var(t2.var_name), t1.var_name),
            t2.type,
        )
        return Conjunction(
            c0,
            implication_constraint(t2.var_name, t2.var_type, c1),
        )
    else:
        logger.error(f"Failed subtyping by exhaustion: {t1} <: {t2}")
        return cfalse
