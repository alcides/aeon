from __future__ import annotations

from collections.abc import Iterable, Iterator
from random import Random
from typing import Callable, TypeVar

from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction, Application, If, Literal, Rec, Term, TypeAbstraction, Var
from aeon.core.types import (
    AbstractionType,
    Kind,
    Type,
    TypeConstructor,
    TypePolymorphism,
    RefinementPolymorphism,
    refined_to_unrefined_type,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.synthesis.modules.tdsyn.bindings import GrammarScope, open_abstraction
from aeon.synthesis.modules.tdsyn.constraints import candidate_feasible, eager_pruning, obligations
from aeon.synthesis.grammar.nonterminals import ExpressionDomain, grammar_bindings
from aeon.synthesis.modules.tdsyn.helpers import (
    base_type_of,
    bases_match,
    get_return_type,
    is_subtype,
    monomorphize,
    is_constructor_term,
)
from aeon.synthesis.modules.tdsyn.library import get_component_library, iter_concrete_vars
from aeon.synthesis.modules.tdsyn.worklist import TypedHole, fresh_hole
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter
from aeon.utils.pprint import AEON_INFIX_OPERATORS

_loc = SynthesizedLocation("tdsyn")

Candidate = tuple[Term, list[TypedHole]]
_T = TypeVar("_T")


def _ordered(items: Iterable[_T], rng: Random | None) -> Iterable[_T]:
    """Randomize cheap production descriptions, before constructing/checking them."""
    if rng is None:
        return items
    result = list(items)
    rng.shuffle(result)
    return result


def get_applicable_functions(
    ctx: TypingContext,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, Type]]:
    """Get all applicable functions from context, monomorphizing polymorphic ones.

    Prefer :func:`get_component_library` for indexed lookups; this remains for
    call sites that need the flat list.
    """
    lib = get_component_library(ctx, skip)
    return [(term, ty) for term, ty in lib.functions]


def _build_application(
    f_term: Term,
    f_type: Type,
    hole: TypedHole,
) -> tuple[Term, list[TypedHole]]:
    """Freshen dependent arguments and carry the result contract down to them."""
    children: list[TypedHole] = []
    result = f_term
    while isinstance(f_type, AbstractionType):
        hole_term, child = fresh_hole(f_type.var_type, hole.context, domain=hole.domain)
        result = Application(result, hole_term, _loc)
        children.append(child)
        f_type = substitution_in_type(f_type.type, Var(child.name), f_type.var_name)

    # symbolic_term/obligations use core liquefaction, which unwraps both type
    # and refinement applications (and preserves already supplied arguments).
    bindings, predicates = obligations(hole, result, children, f_type)
    for child in children:
        child.bindings = dict(bindings)
        child.constraints = list(predicates)
    return result, children


def _compatible_result(ctx: TypingContext, actual: Type, goal: Type) -> bool:
    # Check the full shape, including datatype parameters, before existential
    # feasibility. The dependent outer predicate is checked with its witnesses.
    return bases_match(actual, goal) and is_subtype(
        ctx, refined_to_unrefined_type(actual), refined_to_unrefined_type(goal)
    )


def backward_abs_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Backward abstraction tactic: introduce an abstraction for a function-typed goal.

    Produces ``fun x -> ?body`` where ``?body`` has the goal's codomain type
    with ``x`` in scope. Only applies when the goal is a function type.
    """
    match hole.expected_type:
        case AbstractionType():
            name, body, context = open_abstraction(hole.expected_type, hole.context)
            body_hole_term, body_typed_hole = fresh_hole(body, context, domain=hole.domain)
            return [(Abstraction(name, body_hole_term, _loc), [body_typed_hole])]
        case _:
            return []


def backward_lit_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Backward literal tactic: literal candidates for a base-typed goal."""
    return list(iter_backward_lit_candidates(hole, skip))


def iter_backward_lit_candidates(
    hole: TypedHole, skip: Callable[[Name], bool], rng: Random | None = None
) -> Iterator[Candidate]:
    candidates: list[tuple[Term, list[TypedHole]]] = []
    base = base_type_of(hole.expected_type)
    if base is not None:
        match base:
            case TypeConstructor(Name("Int", _)):
                for ival in range(-2, 11):
                    candidates.append((Literal(ival, t_int, _loc), []))
            case TypeConstructor(Name("Bool", _)):
                candidates.append((Literal(True, t_bool, _loc), []))
                candidates.append((Literal(False, t_bool, _loc), []))
            case TypeConstructor(Name("Float", _)):
                for fval in [-1.0, -0.5, 0.0, 0.5, 1.0, 2.0]:
                    candidates.append((Literal(fval, t_float, _loc), []))
            case TypeConstructor(Name("String", _)):
                # Small fixed set so BFS can close String holes without
                # expanding into recursive string operators first.
                for sval in ("", "a", "b", "hello", " "):
                    candidates.append((Literal(sval, t_string, _loc), []))
            case _:
                pass
    for term, children in _ordered(candidates, rng):
        if candidate_feasible(hole, term, children):
            yield term, children


def backward_close_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Backward close tactic: close the goal with an in-scope variable of the goal's type.

    Same candidates as ``forward_close``: a variable whose type already proves
    the goal closes it regardless of the reasoning direction. Both ids are
    exposed so each direction's tactic menu reads completely.
    """
    return forward_close_candidates(hole, skip)


def backward_app_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Backward application tactic: apply a function whose return type matches the goal.

    Produces ``f(?h1, ..., ?hn)`` for each in-scope (possibly monomorphized)
    function whose return type matches the goal, leaving fresh holes for the
    arguments.
    """
    return list(iter_backward_app_candidates(hole, skip))


def iter_backward_app_candidates(
    hole: TypedHole, skip: Callable[[Name], bool], rng: Random | None = None, *, constructors_only: bool = False
) -> Iterator[Candidate]:
    T = hole.expected_type
    functions = get_component_library(hole.context, skip, hole.nonterminal).functions_returning(T)
    for f_term, f_type in _ordered(functions, rng):
        if constructors_only and not is_constructor_term(f_term):
            continue
        ret_type = get_return_type(f_type)
        if _compatible_result(hole.context, ret_type, T):
            app_term, new_holes = _build_application(f_term, f_type, hole)
            if candidate_feasible(hole, app_term, new_holes):
                yield app_term, new_holes


def backward_if_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Backward if tactic: an if-then-else whose branches are typed by the goal."""
    T = hole.expected_type
    ctx = hole.context
    cond_hole_term, cond_typed_hole = fresh_hole(t_bool, ctx, domain=hole.domain)
    then_hole_term, then_typed_hole = fresh_hole(T, ctx, domain=hole.domain)
    else_hole_term, else_typed_hole = fresh_hole(T, ctx, domain=hole.domain)
    return [
        (
            If(cond_hole_term, then_hole_term, else_hole_term, _loc),
            [cond_typed_hole, then_typed_hole, else_typed_hole],
        )
    ]


def backward_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Backward action: from expected type, find terms that produce a subtype.

    Combines the granular backward tactics. Given hole expecting type T:
    1. If T is a function type, produce an abstraction (and nothing else)
    2. Generate literals for base types
    3. Look up variables with matching types
    4. Find functions whose return type matches T
    5. Generate if-then-else
    """
    abs_candidates = backward_abs_candidates(hole, skip)
    if abs_candidates:
        return abs_candidates  # For function types, only produce abstractions

    candidates: list[tuple[Term, list[TypedHole]]] = []
    candidates.extend(backward_lit_candidates(hole, skip))
    candidates.extend(backward_close_candidates(hole, skip))
    candidates.extend(backward_app_candidates(hole, skip))
    candidates.extend(backward_if_candidates(hole, skip))
    return candidates


def iter_backward_candidates(
    hole: TypedHole, skip: Callable[[Name], bool], rng: Random | None = None, *, constructors_only: bool = False
) -> Iterator[Candidate]:
    if constructors_only:
        yield from iter_forward_close_candidates(hole, skip, rng, constructors_only=True)
        yield from iter_backward_app_candidates(hole, skip, rng, constructors_only=True)
        return
    abstractions = backward_abs_candidates(hole, skip)
    if abstractions:
        yield from abstractions
        return
    yield from iter_backward_lit_candidates(hole, skip, rng)
    yield from iter_forward_close_candidates(hole, skip, rng)
    yield from iter_backward_app_candidates(hole, skip, rng)
    yield from backward_if_candidates(hole, skip)


def _forward_applications(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole], Type]]:
    """Applications of in-scope functions to in-scope variables.

    Given hole expecting type T, for each variable v:A in scope, find functions
    f:(x:A)->B where A is compatible with v's type, and produce f(v) with
    remaining holes if needed, keeping only applications whose result type
    matches T. Returns (term, new_holes, result_type) triples.
    """
    return list(_iter_forward_applications(hole, skip))


def _iter_forward_applications(
    hole: TypedHole, skip: Callable[[Name], bool], rng: Random | None = None
) -> Iterator[tuple[Term, list[TypedHole], Type]]:
    T = hole.expected_type
    ctx = hole.context
    library = get_component_library(ctx, skip, hole.nonterminal)

    for v_name, v_type in _ordered(iter_concrete_vars(ctx, skip, hole.domain), rng):
        for f_term, f_type in _ordered(library.functions_accepting(v_type), rng):
            first_param_type = f_type.var_type

            if not bases_match(v_type, first_param_type):
                continue
            # Random walks also defer the refinement query for an already
            # supplied argument. Their final validator checks the complete
            # application; exhaustively proving every unchosen f(v) is costly.
            compatible = is_subtype if eager_pruning.get() else _compatible_result
            if not compatible(ctx, v_type, first_param_type):
                continue

            applied = Application(f_term, Var(v_name, _loc), _loc)
            remaining_type = substitution_in_type(f_type.type, Var(v_name), f_type.var_name)

            if isinstance(remaining_type, AbstractionType):
                final_ret = get_return_type(remaining_type)
                if not _compatible_result(ctx, final_ret, T):
                    continue
                result, new_holes = _build_application(applied, remaining_type, hole)
                if candidate_feasible(hole, result, new_holes):
                    yield result, new_holes, final_ret
            else:
                if _compatible_result(ctx, remaining_type, T) and candidate_feasible(hole, applied, [], remaining_type):
                    yield applied, [], remaining_type


def forward_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Forward action: from variables in scope, find functions that consume them.

    Given hole expecting type T, for each variable v:A in scope, find functions
    f:(x:A)->B where A is compatible with v's type, and produce f(v) with
    remaining holes if needed.
    """
    return [(term, new_holes) for term, new_holes, _ in _forward_applications(hole, skip)]


def iter_forward_candidates(
    hole: TypedHole, skip: Callable[[Name], bool], rng: Random | None = None
) -> Iterator[Candidate]:
    for term, children, _ in _iter_forward_applications(hole, skip, rng):
        yield term, children


def _let_candidate(
    hole: TypedHole,
    value_term: Term,
    value_holes: list[TypedHole],
    value_type: Type,
) -> tuple[Term, list[TypedHole]]:
    """Wrap a value in ``let v : value_type := value in ?goal``, reopening the
    goal with ``v`` in scope.

    The let is type-annotated (a non-recursive ``Rec``) so the value is
    *checked* against ``value_type`` — values such as abstractions have no
    synthesizable type — and so the demonstrative insertion shows the type the
    step brings into scope.
    """
    level, scope = GrammarScope.from_context(hole.context).bind("v", value_type)
    variable, _ = level.lower(scope)
    v_name = variable.name
    goal_hole_term, goal_typed_hole = fresh_hole(
        hole.expected_type,
        scope.context,
        list(hole.constraints),
        domain=hole.domain,
    )
    return Rec(v_name, value_type, value_term, goal_hole_term, loc=_loc), value_holes + [goal_typed_hole]


def forward_close_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Forward close tactic: close the goal with a variable whose type already proves it.

    Polymorphic nullary constructors (e.g. ``List_nil : forall a. List a``) are
    monomorphized and included when the instantiation matches the goal — needed
    for ADT value generation as well as ordinary type-directed search.
    """
    return list(iter_forward_close_candidates(hole, skip))


def iter_forward_close_candidates(
    hole: TypedHole, skip: Callable[[Name], bool], rng: Random | None = None, *, constructors_only: bool = False
) -> Iterator[Candidate]:
    T = hole.expected_type
    ctx = hole.context
    for term, var_type in _ordered(get_component_library(ctx, skip, hole.nonterminal).values_matching(T), rng):
        if constructors_only and not is_constructor_term(term):
            continue
        if _compatible_result(ctx, var_type, T) and candidate_feasible(hole, term, [], var_type):
            yield term, []


def forward_let_app_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Forward let-application tactic: bind a forward application and reopen the goal.

    Each option ``forward_candidates`` offers becomes a
    ``let v := f(x, ...) in ?goal`` candidate. The let-bound variable gets the
    unrefined result type: dependent refinements on a function's return type
    mention its parameter binders, which are not in scope at the binding site.
    """
    if hole.domain is ExpressionDomain.REFINEMENT:
        return []
    return [
        _let_candidate(hole, value_term, value_holes, refined_to_unrefined_type(value_type))
        for value_term, value_holes, value_type in _forward_applications(hole, skip)
    ]


def forward_let_if_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Forward let-if tactic: bind an if-then-else over the goal type.

    Produces ``let v := if ?c then ?t else ?e in ?goal`` where the branches and
    ``v`` carry the goal's type, so a later step can close the goal with ``v``.
    """
    if hole.domain is ExpressionDomain.REFINEMENT:
        return []
    T = hole.expected_type
    ctx = hole.context
    cond_hole_term, cond_typed_hole = fresh_hole(t_bool, ctx, domain=hole.domain)
    then_hole_term, then_typed_hole = fresh_hole(T, ctx, domain=hole.domain)
    else_hole_term, else_typed_hole = fresh_hole(T, ctx, domain=hole.domain)
    value = If(cond_hole_term, then_hole_term, else_hole_term, _loc)
    return [_let_candidate(hole, value, [cond_typed_hole, then_typed_hole, else_typed_hole], T)]


def forward_let_tapp_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Forward let-type-application tactic: instantiate a polymorphic variable.

    For each polymorphic variable in scope and each of its monomorphic
    instantiations, produces ``let v : T := f in ?goal``, bringing the
    instantiated (usually function-typed) ``v`` into scope. Operator-named
    variables (``==``, ``+``, ...) print as operator sections (``(=)``,
    ``(+)``, ...).
    """
    if hole.domain is ExpressionDomain.REFINEMENT:
        return []
    ctx = hole.context
    candidates: list[tuple[Term, list[TypedHole]]] = []
    for name, var_type in grammar_bindings(ctx, hole.domain):
        if skip(name):
            continue
        # Only variables with a printable surface form: identifiers, or the
        # standard infix operators (printed as sections). Exotic names such
        # as ``$`` have no parseable spelling as a bare value.
        if not (name.pretty().isidentifier() or name.pretty() in AEON_INFIX_OPERATORS):
            continue
        if not isinstance(var_type, (TypePolymorphism, RefinementPolymorphism)):
            continue
        for value_term, mono_type in monomorphize(name, var_type, ctx):
            candidates.append(_let_candidate(hole, value_term, [], mono_type))
    return candidates


def forward_let_abs_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Forward let-abstraction tactic: bind a function producing the goal type.

    For each built-in base domain type, produces
    ``let v := (fun x -> ?body) in ?goal`` where ``?body`` has the goal's type
    with ``x`` in scope, so ``v : (x:domain) -> goal``.
    """
    if hole.domain is ExpressionDomain.REFINEMENT:
        return []
    T = hole.expected_type
    ctx = hole.context
    candidates: list[tuple[Term, list[TypedHole]]] = []
    for domain in (t_int, t_bool, t_float):
        level, scope = GrammarScope.from_context(ctx).bind("x", domain)
        variable, _ = level.lower(scope)
        x_name = variable.name
        body_hole_term, body_typed_hole = fresh_hole(T, scope.context, domain=hole.domain)
        value = Abstraction(x_name, body_hole_term, _loc)
        candidates.append(_let_candidate(hole, value, [body_typed_hole], AbstractionType(x_name, domain, T)))
    return candidates


def forward_let_tabs_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Forward let-type-abstraction tactic: bind a type-polymorphic value.

    Produces ``let v := (Λa:B. ?body) in ?goal`` where ``?body`` has the goal's
    type with the type variable ``a`` in scope, so ``v : forall a:B, goal``.
    """
    if hole.domain is ExpressionDomain.REFINEMENT:
        return []
    T = hole.expected_type
    ctx = hole.context
    a_name = Name("a", fresh_counter.fresh())
    body_hole_term, body_typed_hole = fresh_hole(T, ctx.with_typevar(a_name, Kind.BASE), domain=hole.domain)
    value = TypeAbstraction(a_name, Kind.BASE, body_hole_term, _loc)
    return [_let_candidate(hole, value, [body_typed_hole], TypePolymorphism(a_name, Kind.BASE, T))]
