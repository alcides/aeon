from __future__ import annotations

from typing import Callable

from aeon.core.instantiation import type_substitution
from aeon.core.terms import Term, TypeApplication, Var
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
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.utils.name import Name
from aeon.verification.sub import sub


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
    current_metadata = metadata.get(fun_name, {})
    vars_to_ignore = current_metadata.get("hide", [])
    if name.name in {v.name for v in vars_to_ignore}:
        return True
    if name.name.startswith("__internal__"):
        return True
    if name.name in ("native", "native_import", "print"):
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
    """
    match ty:
        case TypePolymorphism(var_name, _, body):
            concrete_types = _collect_concrete_types(ctx)
            results: list[tuple[Term, Type]] = []
            for concrete_type in concrete_types:
                substituted = type_substitution(body, var_name, concrete_type)
                term = TypeApplication(Var(name), concrete_type)
                if isinstance(substituted, TypePolymorphism):
                    # Nested polymorphism: recurse (need a fresh name for the intermediate)
                    for sub_term, sub_type in _monomorphize_term(term, substituted, ctx):
                        results.append((sub_term, sub_type))
                else:
                    results.append((term, substituted))
            return results
        case RefinementPolymorphism():
            return []
        case _:
            return [(Var(name), ty)]


def _monomorphize_term(base_term: Term, ty: Type, ctx: TypingContext) -> list[tuple[Term, Type]]:
    """Continue monomorphizing an already partially applied term."""
    match ty:
        case TypePolymorphism(var_name, _, body):
            concrete_types = _collect_concrete_types(ctx)
            results: list[tuple[Term, Type]] = []
            for concrete_type in concrete_types:
                substituted = type_substitution(body, var_name, concrete_type)
                term = TypeApplication(base_term, concrete_type)
                if isinstance(substituted, TypePolymorphism):
                    for sub_term, sub_type in _monomorphize_term(term, substituted, ctx):
                        results.append((sub_term, sub_type))
                else:
                    results.append((term, substituted))
            return results
        case _:
            return [(base_term, ty)]


def make_skip_fn(fun_name: Name, metadata: Metadata) -> Callable[[Name], bool]:
    """Create a skip function for use in actions."""
    current_metadata = metadata.get(fun_name, {})
    is_recursion_allowed = current_metadata.get("recursion", False)

    def skip(name: Name) -> bool:
        return should_skip(name, fun_name, metadata, is_recursion_allowed)

    return skip
