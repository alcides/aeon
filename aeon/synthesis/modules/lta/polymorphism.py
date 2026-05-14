"""Polymorphic transition construction and type instantiation (Paper §3.2,
footnote 5, and §5).

The paper's λ_lta supports parametric polymorphism (type abstractions
`forall α:B, τ`) and abstract refinements (`forall <ρ:s→Bool>, τ`). The LTA
construction rules "extend naturally to these abstractions and their
corresponding type and refinement applications."

Operationally, a polymorphic library function is a *template*: a concrete
candidate term is obtained by instantiating its type variables. The cyclic
LTA of §5 represents the (unbounded) instantiation space compactly; this
module performs the *bounded* instantiation that materializes concrete terms,
driven by the finite `type universe` collected from the query and library.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from aeon.core.instantiation import type_substitution
from aeon.core.substitutions import instantiate_refinement_in_type
from aeon.core.terms import (
    Abstraction,
    Literal,
    RefinementApplication,
    Term,
    TypeApplication,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    refined_to_unrefined_type,
    t_bool,
    t_int,
    t_float,
    t_string,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("lta")


def _trivial_true_predicate() -> Abstraction:
    """The trivially-true refinement predicate `λy. true`, as the term-level
    `Abstraction` shape that `instantiate_refinement_in_type` expects."""
    y = Name("_lta_rho", fresh_counter.fresh())
    return Abstraction(y, Literal(True, t_bool, _loc), _loc)


BUILTIN_BASE_TYPES: list[TypeConstructor] = [t_int, t_bool, t_float, t_string]


# Type universe ------------------------------------------------------------


def collect_type_universe(ctx: TypingContext, goal_type: Type) -> list[Type]:
    """Collect the finite set of concrete base types reachable from the
    library context and the query — the `unrolling' of the cyclic universe
    state `qt`.

    This is what polymorphic type variables get instantiated with.
    """
    seen: set[str] = set()
    universe: list[Type] = []

    def add(t: Type) -> None:
        bt = _base_constructor(t)
        if bt is None:
            return
        key = repr(bt)
        if key not in seen:
            seen.add(key)
            universe.append(bt)

    for tc in BUILTIN_BASE_TYPES:
        add(tc)
    for _, ty in ctx.concrete_vars():
        for sub in _mentioned_types(ty):
            add(sub)
    for sub in _mentioned_types(goal_type):
        add(sub)
    return universe


def _base_constructor(t: Type) -> TypeConstructor | None:
    """Strip refinement to the underlying `TypeConstructor`, if any."""
    u = refined_to_unrefined_type(t)
    return u if isinstance(u, TypeConstructor) else None


def _mentioned_types(t: Type) -> Iterable[Type]:
    """All sub-types syntactically mentioned in `t`."""
    match t:
        case RefinedType(_, inner, _, _):
            yield t
            yield from _mentioned_types(inner)
        case AbstractionType(_, vt, rt, _):
            yield from _mentioned_types(vt)
            yield from _mentioned_types(rt)
        case TypePolymorphism(_, _, body, _):
            yield from _mentioned_types(body)
        case RefinementPolymorphism(_, _, body, _):
            yield from _mentioned_types(body)
        case TypeConstructor(_, args, _):
            yield t
            for a in args:
                yield from _mentioned_types(a)
        case _:
            yield t


# Monomorphization ---------------------------------------------------------


@dataclass(frozen=True)
class Instantiation:
    """A concrete instantiation of a (possibly polymorphic) library binding.

    `term` is the head term — `Var(f)` for monomorphic bindings, or a nest of
    `TypeApplication`/`RefinementApplication` for instantiated ones.
    `mono_type` is the resulting monomorphic type.
    """

    term: Term
    mono_type: Type


def monomorphize(
    name: Name,
    ty: Type,
    universe: list[Type],
    max_instantiations: int = 16,
) -> list[Instantiation]:
    """Enumerate the monomorphic instantiations of `name : ty`.

    - Non-polymorphic types yield a single `Instantiation(Var(name), ty)`.
    - `TypePolymorphism` instantiates the type variable with every type in
      `universe` (recursing for nested `forall`s).
    - `RefinementPolymorphism` instantiates the abstract refinement variable
      with the trivially-true predicate. (Richer abstract-refinement
      enumeration is future work — see module docstring.)
    """
    return list(_mono(Var(name, _loc), ty, universe, max_instantiations))


def _mono(
    head: Term,
    ty: Type,
    universe: list[Type],
    budget: int,
) -> Iterable[Instantiation]:
    if budget <= 0:
        return
    match ty:
        case TypePolymorphism(var_name, _, body, _):
            count = 0
            for concrete in universe:
                if count >= budget:
                    break
                substituted = type_substitution(body, var_name, concrete)
                applied = TypeApplication(head, concrete, _loc)
                if isinstance(substituted, (TypePolymorphism, RefinementPolymorphism)):
                    yield from _mono(applied, substituted, universe, budget - count)
                else:
                    yield Instantiation(applied, substituted)
                count += 1
        case RefinementPolymorphism(pred_name, _sort, body, _):
            # Instantiate the abstract refinement with `λy. true` — sound, but
            # a coarse approximation of the cyclic `qϕ` universe (richer
            # abstract-refinement enumeration is future work; see docstring).
            pred = _trivial_true_predicate()
            try:
                substituted = instantiate_refinement_in_type(body, pred_name, pred)
            except Exception:
                # If the abstract refinement cannot be inlined, fall back to
                # the (already weaker) body with the predicate left abstract.
                substituted = body
            r_applied: Term = RefinementApplication(head, pred, _loc)
            if isinstance(substituted, (TypePolymorphism, RefinementPolymorphism)):
                yield from _mono(r_applied, substituted, universe, budget)
            else:
                yield Instantiation(r_applied, substituted)
        case _:
            yield Instantiation(head, ty)


def is_polymorphic(ty: Type) -> bool:
    return isinstance(ty, (TypePolymorphism, RefinementPolymorphism))
