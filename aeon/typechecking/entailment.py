from __future__ import annotations


from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, ExistentialType
from aeon.core.types import BaseType
from aeon.core.types import extract_parts
from aeon.core.types import TypePolymorphism
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypeBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import UninterpretedBinder
from aeon.typechecking.context import VariableBinder
from aeon.verification.horn import solve
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import UninterpretedFunctionDeclaration


def entailment(ctx: TypingContext, c: Constraint) -> bool:
    match ctx:
        case EmptyContext():
            r = solve(c)
            return r
        case VariableBinder(prev=prev, name=name, type=ty):
            match ty:
                case AbstractionType(var_name=_, var_type=_, type=_):
                    # Functions are not passed into SMT
                    return entailment(prev, c)
                case TypePolymorphism(name=_, kind=_, body=_):
                    # TODO: TypePolymorphism is not passed to SMT.
                    # TODO: Consider using a custom Sort.
                    return entailment(prev, c)
                case ExistentialType(var_name=vname, var_type=vtype, type=ity):
                    return entailment(VariableBinder(VariableBinder(prev, name, ity), vname, vtype), c)
                case _:
                    (name, base, cond) = extract_parts(ty)
                    assert isinstance(base, BaseType)
                    ncond = substitution_in_liquid(cond, LiquidVar(ctx.name), name)
                    return entailment(ctx.prev, Implication(ctx.name, base, ncond, c))
        case TypeBinder(type_name=_, type_kind=_):
            # TODO: Handle TypeBinder in entailment.
            # TODO: Solution is to create a custom sort.
            return entailment(ctx.prev, c)
        case UninterpretedBinder(prev=prev, name=name, type=ty):
            return entailment(
                ctx.prev,
                UninterpretedFunctionDeclaration(ctx.name, ctx.type, c),
            )
        case _:
            assert False
