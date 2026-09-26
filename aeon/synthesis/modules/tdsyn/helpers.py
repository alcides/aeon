from __future__ import annotations

from typing import Callable

from aeon.core.instantiation import type_substitution
from aeon.core.substitutions import instantiate_refinement_in_type
from aeon.core.terms import (
    Abstraction,
    ImplicitRefinementHole,
    Literal,
    RefinementApplication,
    Term,
    TypeApplication,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    refined_to_unrefined_type,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.grammar.utils import SYNTHESIS_EXCLUDED_NAMES
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter
from aeon.verification.sub import sub

_loc = SynthesizedLocation("tdsyn")


def _trivial_true_predicate() -> Abstraction:
    """``λy. true`` — used only to weaken the *candidate type* while the term
    still carries an ``ImplicitRefinementHole`` for Horn inference."""
    y = Name("_pred_y", fresh_counter.fresh())
    return Abstraction(y, Literal(True, t_bool, _loc), _loc)


def is_subtype(ctx: TypingContext, t1: Type, t2: Type) -> bool:
    """Check if t1 is a subtype of t2 using SMT-based verification."""
    constraint = sub(ctx, t1, t2)
    return entailment(ctx, constraint)


def base_type_of(ty: Type) -> TypeConstructor | None:
    """Strip refinements to get the base TypeConstructor, or None if not a base type."""
    unrefined = refined_to_unrefined_type(ty)
    match unrefined:
        case TypeConstructor():
            return unrefined
        case _:
            return None


def get_return_type(ty: Type) -> Type:
    """Get the final return type of a (possibly multi-argument) function type."""
    t = ty
    while isinstance(t, AbstractionType):
        t = t.type
    return t


def get_param_types(ty: Type) -> list[tuple[Name, Type]]:
    """Extract (name, type) for each parameter of a function type."""
    params: list[tuple[Name, Type]] = []
    t = ty
    while isinstance(t, AbstractionType):
        params.append((t.var_name, t.var_type))
        t = t.type
    return params


def bases_match(t1: Type, t2: Type) -> bool:
    """Fast structural pre-check: do the base type constructors match?"""
    b1 = base_type_of(t1)
    b2 = base_type_of(t2)
    if b1 is None or b2 is None:
        return False
    return b1.name.name == b2.name.name


def should_skip(name: Name, fun_name: Name, metadata: Metadata, is_recursion_allowed: bool) -> bool:
    """Check if a variable should be skipped during synthesis."""
    if name == fun_name:
        return not is_recursion_allowed
    if name.name in SYNTHESIS_EXCLUDED_NAMES:
        return True
    return False


BUILTIN_BASE_TYPES: list[TypeConstructor] = [t_int, t_bool, t_float, t_string]


def _collect_concrete_types(ctx: TypingContext) -> list[TypeConstructor]:
    """Collect all concrete base types from context plus built-ins."""
    types: set[str] = set()
    result: list[TypeConstructor] = []
    for tc in BUILTIN_BASE_TYPES:
        if tc.name.name not in types:
            types.add(tc.name.name)
            result.append(tc)
    for _, t in ctx.concrete_vars():
        bt = base_type_of(t)
        if bt is not None and bt.name.name not in types and bt != TypeConstructor(Name("Unit", 0)):
            types.add(bt.name.name)
            result.append(bt)
    return result


def monomorphize(name: Name, ty: Type, ctx: TypingContext) -> list[tuple[Term, Type]]:
    """Generate all monomorphic instantiations of a (possibly polymorphic) type.

    Returns list of (term, monomorphic_type) pairs.
    For non-polymorphic types, returns [(Var(name), ty)].
    For polymorphic types, instantiates type variables with concrete types from context.
    Abstract refinement quantifiers (``forall <p>``) are opened with an
    ``ImplicitRefinementHole``, matching elaboration: Horn inference fills in
    ``p`` when the finished term is typechecked.
    """
    return _monomorphize_term(Var(name, _loc), ty, ctx)


def _monomorphize_term(base_term: Term, ty: Type, ctx: TypingContext) -> list[tuple[Term, Type]]:
    """Continue monomorphizing an already partially applied term."""
    match ty:
        case TypePolymorphism(var_name, _, body):
            concrete_types = _collect_concrete_types(ctx)
            results: list[tuple[Term, Type]] = []
            for concrete_type in concrete_types:
                substituted = type_substitution(body, var_name, concrete_type)
                applied: Term = TypeApplication(base_term, concrete_type, _loc)
                results.extend(_monomorphize_term(applied, substituted, ctx))
            return results
        case RefinementPolymorphism(pred_name, _sort, body):
            # Match elaboration: open ``forall <p>`` with an implicit hole on the
            # *term* so Horn inference can instantiate ``p`` at typecheck time.
            # The candidate type used for search is weakened with ``λy. true``
            # (same approximation as LTA) so argument holes stay SMT-friendly.
            hole = ImplicitRefinementHole(Name("_pred", fresh_counter.fresh()), _loc)
            applied = RefinementApplication(base_term, hole, _loc)
            substituted = instantiate_refinement_in_type(body, pred_name, _trivial_true_predicate())
            return _monomorphize_term(applied, substituted, ctx)
        case _:
            return [(base_term, ty)]


def make_skip_fn(fun_name: Name, metadata: Metadata) -> Callable[[Name], bool]:
    """Create a skip function for use in actions."""
    current_metadata = metadata.get(fun_name, {})
    is_recursion_allowed = current_metadata.get("recursion", False)

    def skip(name: Name) -> bool:
        return should_skip(name, fun_name, metadata, is_recursion_allowed)

    return skip
