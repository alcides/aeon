from __future__ import annotations

from loguru import logger

from aeon.core.liquid import LiquidLiteralBool, LiquidVar
from aeon.core.substitutions import substitute_vartype, substitution_in_liquid
from aeon.core.types import AbstractionType, TypeConstructor
from aeon.core.types import BaseType
from aeon.core.types import Type
from aeon.core.types import extract_parts
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypeBinder, TypeConstructorBinder, UninterpretedFunctionBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.verification.helpers import pretty_print_constraint
from aeon.verification.horn import solve
from aeon.verification.vcs import Constraint, UninterpretedFunctionDeclaration
from aeon.verification.vcs import Implication

ctrue = LiquidLiteralBool(True)
t_int = BaseType("Int")  # TODO: Create a Singleton for Monomorphic

MONOMORPHIC_PLACEHOLDER = BaseType("TypePolymorphismPlaceHolder")


def monomorphise(ty: AbstractionType | TypePolymorphism) -> Type:
    """Converts a (possibly) polymorphic function into monomorphic."""
    match ty:
        case TypePolymorphism(name=n, kind=_, body=b):
            b2 = substitute_vartype(b, MONOMORPHIC_PLACEHOLDER, n)
            return monomorphise(b2)
        case TypeConstructor(name=n, args=_):
            return BaseType(n)
        case _:
            return ty


def entailment(ctx: TypingContext, c: Constraint):
    for entry in reversed(ctx.entries):
        match entry:
            case TypeBinder(name=_, kind=_):
                pass
            case UninterpretedFunctionBinder(name=n, type=ty):
                monoty = monomorphise(ty)
                assert isinstance(monoty, AbstractionType)
                c = UninterpretedFunctionDeclaration(n, monoty, c)
            case VariableBinder(name=_, type=TypePolymorphism(name=_, kind=_, body=_)):
                pass
            case VariableBinder(name=_, type=AbstractionType(var_name=_, var_type=_, type=_)):
                pass
            case VariableBinder(name=name, type=TypeVar(name=_)):
                c = Implication(name, t_int, ctrue, c)
            case VariableBinder(name=name, type=ty):
                (ref_name, base, cond) = extract_parts(ty)
                if isinstance(base, BaseType):
                    ncond = substitution_in_liquid(cond, LiquidVar(name), ref_name)
                    c = Implication(name, base, ncond, c)
                else:
                    assert False
            case TypeConstructorBinder(name=name, type_parameters=_):
                pass
            case _:
                assert False

    r = solve(c)
    if not r:
        logger.error("Could not show constrain:")
        logger.error(pretty_print_constraint(c))
        logger.error(c)
    return r
