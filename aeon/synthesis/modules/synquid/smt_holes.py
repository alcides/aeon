"""SMT-driven completion for synquid's two-step shape-then-fill pipeline.

Phase 1 (in :mod:`aeon.synthesis.modules.synquid.engine`): enumerate term
*shapes* with placeholders ``Annotation(Hole(name), Int|Float)`` wherever
a literal would otherwise be eagerly enumerated. This collapses the
20-million-Float-literal level-0 explosion into a single placeholder per
type per generator.

Phase 2 (this module): when synquid has a complete term shape, walk it,
collect the placeholders, ask z3 to find values that satisfy any
refinement constraints in scope (via tdsyn's :func:`solve_literals`),
substitute the model back, and hand the concrete term to ``validate`` /
``evaluate``. When z3 has no constraints to work with — common for
example-driven fitness — we fall back to a small canonical seed list per
type so the search doesn't stall on default zeros.
"""

from __future__ import annotations

from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    Term,
    TypeAbstraction,
    TypeApplication,
)
from aeon.core.types import (
    RefinedType,
    Type,
    TypeConstructor,
    t_bool,
    t_float,
    t_int,
)
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.modules.tdsyn.worklist import TypedHole
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("synquid_smt")


# Canonical seed values used when z3 returns no constraints for a hole.
# Small and curated — matches what tdsyn yields at level 0 for the same
# types, so synquid's behaviour is consistent in the no-refinement case.
_SEED_INT = [0, 1, -1, 2, 10]
_SEED_FLOAT = [0.0, 1.0, -1.0, 0.5, 2.0]
_SEED_BOOL = [True, False]


def _base_name(ty: Type) -> str | None:
    match ty:
        case TypeConstructor(Name(name, _)):
            return name
        case RefinedType(_, TypeConstructor(Name(name, _)), _):
            return name
        case _:
            return None


def collect_placeholders(term: Term) -> list[tuple[Name, Type]]:
    """Return every ``(hole_name, expected_type)`` pair embedded as
    ``Annotation(Hole(name), expected_type)`` inside ``term`` (in order)."""
    found: list[tuple[Name, Type]] = []
    _walk_collect(term, found)
    return found


def _walk_collect(term: Term, found: list[tuple[Name, Type]]) -> None:
    if isinstance(term, Annotation):
        if isinstance(term.expr, Hole):
            found.append((term.expr.name, term.type))
        else:
            _walk_collect(term.expr, found)
    elif isinstance(term, Application):
        _walk_collect(term.fun, found)
        _walk_collect(term.arg, found)
    elif isinstance(term, If):
        _walk_collect(term.cond, found)
        _walk_collect(term.then, found)
        _walk_collect(term.otherwise, found)
    elif isinstance(term, Abstraction):
        _walk_collect(term.body, found)
    elif isinstance(term, TypeApplication):
        _walk_collect(term.body, found)
    elif isinstance(term, TypeAbstraction):
        _walk_collect(term.body, found)
    elif isinstance(term, Let):
        _walk_collect(term.var_value, found)
        _walk_collect(term.body, found)
    elif isinstance(term, Rec):
        _walk_collect(term.var_value, found)
        _walk_collect(term.body, found)


def fill_placeholders(term: Term, mapping: dict[Name, Term]) -> Term:
    """Replace every ``Annotation(Hole(name), _)`` whose name is in
    ``mapping`` with the corresponding literal."""
    if isinstance(term, Annotation):
        if isinstance(term.expr, Hole) and term.expr.name in mapping:
            return mapping[term.expr.name]
        return Annotation(fill_placeholders(term.expr, mapping), term.type, term.loc)
    if isinstance(term, Application):
        return Application(
            fill_placeholders(term.fun, mapping),
            fill_placeholders(term.arg, mapping),
            term.loc,
        )
    if isinstance(term, If):
        return If(
            fill_placeholders(term.cond, mapping),
            fill_placeholders(term.then, mapping),
            fill_placeholders(term.otherwise, mapping),
            term.loc,
        )
    if isinstance(term, Abstraction):
        return Abstraction(term.var_name, fill_placeholders(term.body, mapping), term.loc)
    if isinstance(term, TypeApplication):
        return TypeApplication(fill_placeholders(term.body, mapping), term.type, term.loc)
    return term


def _seed_literal(ty: Type, idx: int) -> Term | None:
    """Pick the ``idx``-th canonical seed value for ``ty``. Returns
    ``None`` if the type has no canonical seed."""
    name = _base_name(ty)
    match name:
        case "Int":
            return Literal(_SEED_INT[idx % len(_SEED_INT)], t_int, _loc)
        case "Float":
            return Literal(_SEED_FLOAT[idx % len(_SEED_FLOAT)], t_float, _loc)
        case "Bool":
            return Literal(_SEED_BOOL[idx % len(_SEED_BOOL)], t_bool, _loc)
        case _:
            return None


def freshen_placeholders(term: Term) -> Term:
    """Re-stamp every ``Annotation(Hole, T)`` with a fresh unique id.

    Phase 1 yields placeholders with a deterministic id (so the engine's
    ``mem`` cache is safe to identity-compare), but a single shape can
    contain many copies of the *same* cached placeholder — e.g. an
    ``if`` whose ``then`` and ``else`` both pulled the level-0 Float
    placeholder from the cache. Without freshening, those would all share
    a single ``Hole`` name, and the substitution step would fill them
    with the same value, collapsing the branch. We rename here so each
    textual occurrence is independent.
    """
    if isinstance(term, Annotation) and isinstance(term.expr, Hole):
        new_name = Name(term.expr.name.name, fresh_counter.fresh())
        return Annotation(Hole(new_name, term.expr.loc), term.type, term.loc)
    if isinstance(term, Annotation):
        return Annotation(freshen_placeholders(term.expr), term.type, term.loc)
    if isinstance(term, Application):
        return Application(
            freshen_placeholders(term.fun),
            freshen_placeholders(term.arg),
            term.loc,
        )
    if isinstance(term, If):
        return If(
            freshen_placeholders(term.cond),
            freshen_placeholders(term.then),
            freshen_placeholders(term.otherwise),
            term.loc,
        )
    if isinstance(term, Abstraction):
        return Abstraction(term.var_name, freshen_placeholders(term.body), term.loc)
    if isinstance(term, TypeApplication):
        return TypeApplication(freshen_placeholders(term.body), term.type, term.loc)
    return term


def smt_complete(term: Term, ctx: TypingContext, seed_idx: int = 0) -> Term | None:
    """Replace every ``Annotation(Hole, T)`` in ``term`` with a concrete
    ``Literal``.

    Tries z3 first via :func:`solve_literals`. If z3 returns no model
    (typical when there are no refinement constraints), falls back to
    ``_seed_literal`` for each placeholder. ``seed_idx`` lets the caller
    cycle through canonical values when iterating the same shape with
    different defaults.

    Returns the completed term, or ``None`` when at least one placeholder
    has a type we don't know how to fill (in which case the caller should
    skip the candidate).
    """
    placeholders = collect_placeholders(term)
    if not placeholders:
        return term

    # Freshen so duplicate placeholder names from mem-cache reuse become
    # independent before we hand them to z3 / the seed table.
    term = freshen_placeholders(term)
    placeholders = collect_placeholders(term)

    # Try SMT first. Re-uses tdsyn's helper, which expects TypedHole
    # inputs; we synthesise them with the synquid-side context.
    typed_holes = [
        TypedHole(name=name, expected_type=ty, context=ctx)
        for (name, ty) in placeholders
    ]
    mapping: dict[Name, Term] = {}
    try:
        models = solve_literals(typed_holes, max_models=1)
    except Exception:
        models = []
    if models:
        mapping.update(models[0])

    # Fall back to canonical seed values for any hole z3 didn't constrain.
    for name, ty in placeholders:
        if name in mapping:
            continue
        lit = _seed_literal(ty, seed_idx)
        if lit is None:
            return None
        mapping[name] = lit

    return fill_placeholders(term, mapping)
