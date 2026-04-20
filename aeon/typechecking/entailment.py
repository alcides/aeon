from __future__ import annotations

from aeon.utils.name import Name
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType
from aeon.core.types import RefinementPolymorphism
from aeon.core.types import TypeConstructor
from aeon.core.types import extract_parts
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypeConstructorBinder
from aeon.typechecking.context import TypeBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import UninterpretedBinder
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.verification.horn import solve
from aeon.verification.sub import is_first_order_function
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import UninterpretedFunctionDeclaration

from aeon.core.liquid_ops import ops


def entailment_context(ctx: TypingContext, c: Constraint) -> Constraint:
    for entry in ctx.entries[::-1]:
        match entry:
            case VariableBinder(name, AbstractionType(vname, vtype, rtype)):
                if name in ops:
                    pass
                elif is_first_order_function(AbstractionType(vname, vtype, rtype)):
                    c = UninterpretedFunctionDeclaration(name, AbstractionType(vname, vtype, rtype), c)
                else:
                    pass
            case VariableBinder(name, TypePolymorphism(_, _, _)):
                if name in ops:
                    pass
                else:
                    # Polymorphic binders are skipped here: entailment_context does not yet
                    # lift them into Horn declarations (see Synquid roadmap / issue tracker).
                    pass
            case VariableBinder(name, RefinementPolymorphism(_, _, _)):
                if name in ops:
                    pass
                else:
                    # Refinement-polymorphic binders are skipped (same limitation as above).
                    pass
            case VariableBinder(name, ty):
                (nname, base, cond) = extract_parts(ty)
                match base:
                    case TypeConstructor(_, []) | TypeVar(_):
                        ncond = substitution_in_liquid(cond, LiquidVar(name), nname)
                        c = Implication(name, base, ncond, c)
                    case TypeConstructor(_, _):
                        ncond = substitution_in_liquid(cond, LiquidVar(name), nname)
                        c = Implication(name, TypeConstructor(Name("Int", 0), []), ncond, c)
                    case _:
                        assert False, f"Unknown base: {base}"
            case TypeBinder(_, _):
                # Type-level binders do not introduce a value assumption into the
                # liquid VC until we have a Horn story for kind-polymorphic binders
                # (see TypePolymorphism / RefinementPolymorphism cases above). Keeping
                # this a no-op is sound: constraints mentioning the bound type variable
                # are resolved in ``check`` before entailment sees them, or remain
                # ill-scoped if misused.
                pass
            case UninterpretedBinder(name, type):
                c = UninterpretedFunctionDeclaration(name, type, c)
            case TypeConstructorBinder(name, _):
                pass
            case _:
                assert False, f"Untreated {ctx}."
    return c


def entailment(ctx: TypingContext, c: Constraint) -> bool:
    c = entailment_context(ctx, c)
    atoms = extract_qualifier_atoms(ctx)
    return solve(c, typing_ctx=ctx, qualifier_atoms=atoms)
