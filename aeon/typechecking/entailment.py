from __future__ import annotations

from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import extract_parts
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypeBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import UninterpretedBinder
from aeon.typechecking.context import VariableBinder
from aeon.verification.horn import solve
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import UninterpretedFunctionDeclaration

from aeon.core.liquid_ops import all_ops


def entailment(ctx: TypingContext, c: Constraint):
    match ctx:
        case EmptyContext():
            return solve(c)
        case VariableBinder(prev, name, AbstractionType(vname, vtype, rtype)):
            if name in all_ops:
                return entailment(prev, c)
            else:
                return entailment(prev, UninterpretedFunctionDeclaration(name, AbstractionType(vname, vtype, rtype), c))

        case VariableBinder(prev, name, TypePolymorphism(_, _, _)):
            return entailment(prev, c)
        case VariableBinder(prev, name, ty):
            (name, base, cond) = extract_parts(ty)
            if isinstance(base, BaseType):
                ncond = substitution_in_liquid(cond, LiquidVar(ctx.name), name)
                return entailment(
                    ctx.prev,
                    Implication(ctx.name, base, ncond, c),
                )
            elif isinstance(ctx.type, TypeVar):
                assert False  # TypeVars are being replaced by Int
            else:
                assert False
        case TypeBinder(prev, name, _):
            return entailment(prev, c)
            # TODO: Consider passing as a concrete placeholder type for SMT
        case UninterpretedBinder(prev, name, type):
            return entailment(
                prev,
                UninterpretedFunctionDeclaration(name, type, c),
            )
        case _:
            assert False
