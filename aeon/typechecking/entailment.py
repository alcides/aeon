from __future__ import annotations

from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import extract_parts
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypeConstructorBinder
from aeon.typechecking.context import TypeBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import UninterpretedBinder
from aeon.typechecking.context import VariableBinder
from aeon.verification.horn import solve
from aeon.verification.sub import is_first_order_function
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import UninterpretedFunctionDeclaration

from aeon.core.liquid_ops import ops


def entailment(ctx: TypingContext, c: Constraint) -> bool:
    for entry in ctx.entries:
        match entry:
            case VariableBinder(name, AbstractionType(vname, vtype, rtype)):
                if name in ops:
                    pass
                elif is_first_order_function(AbstractionType(vname, vtype, rtype)):
                    c = UninterpretedFunctionDeclaration(name, AbstractionType(vname, vtype, rtype), c)
            case VariableBinder(name, TypePolymorphism(_, _, _)):
                if name in ops:
                    pass
                else:
                    # TODO: polymorphism
                    # Right now we are ignoring lifting functions with polymorphism
                    pass
            case VariableBinder(name, ty):
                (nname, base, cond) = extract_parts(ty)
                match base:
                    case BaseType(_):
                        ncond = substitution_in_liquid(cond, LiquidVar(name),
                                                    nname)
                        c = Implication(name, base, ncond, c)
                    case TypeVar(_):
                        assert False
                    case _:
                        assert False, f"Unknown base: {base}"
            case TypeBinder(name, _):
                pass
                # TODO: Consider passing as a concrete placeholder type for SMT
            case UninterpretedBinder(name, type):
                c = UninterpretedFunctionDeclaration(name, type, c)
            case TypeConstructorBinder(name, _):
                pass
            case _:
                assert False, f"Untreated {ctx}."
    return solve(c)
