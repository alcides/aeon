from __future__ import annotations

from collections.abc import Iterable, Iterator
from itertools import chain
from random import Random
from time import monotonic
from typing import Callable, TypeVar

from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction, Application, If, Literal, Rec, Term, TypeAbstraction, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    Kind,
    RefinedType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar as CoreTypeVar,
    RefinementPolymorphism,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.synthesis.modules.tdsyn.bindings import GrammarScope, open_abstraction
from aeon.synthesis.modules.tdsyn.constraints import (
    candidate_feasible,
    deadline,
    eager_pruning,
    has_refinement,
    obligations,
)
from aeon.synthesis.grammar.nonterminals import ExpressionDomain, grammar_bindings
from aeon.synthesis.modules.tdsyn.helpers import (
    base_type_of,
    bases_match,
    get_return_type,
    is_subtype,
    monomorphize,
    is_constructor_term,
    is_eliminator_term,
    shapes_match,
)
from aeon.synthesis.modules.tdsyn.library import get_component_library, iter_concrete_vars
from aeon.synthesis.modules.tdsyn.worklist import TypedHole, fresh_hole, substitute_holes_map
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
    # Formal arguments are not in scope yet. Nested contracts (e.g. an array
    # element equal to an argument) are as dependent as the outer refinement.
    # Bind witnesses before checking contracts; never send this open result
    # type to SMT. Keep datatype parameters in the cheap structural check.
    return shapes_match(actual, goal)


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


# One then-arm per refined goal. Further arms would re-run Horn abduction on
# every constructor spine; the first realized guard is the branch-first step.
_ABDUCTION_ATTEMPTS = 8
_ABDUCTION_SECONDS = 1.0

_RELATIONS = (
    Name("==", 0),
    Name("!=", 0),
    Name("<", 0),
    Name("<=", 0),
    Name(">", 0),
    Name(">=", 0),
)


def _refined_goal(hole: TypedHole) -> bool:
    return hole.domain is ExpressionDomain.TERM and has_refinement(hole.expected_type)


def _type_argument(pattern: Type, actual: Type, variable: Name) -> Type | None:
    """The instance of ``variable`` that makes ``pattern`` match ``actual``."""
    if isinstance(pattern, CoreTypeVar) and pattern.name == variable:
        return actual
    if isinstance(pattern, RefinedType):
        return _type_argument(pattern.type, actual, variable)
    if isinstance(actual, RefinedType):
        return _type_argument(pattern, actual.type, variable)
    if isinstance(pattern, TypeConstructor) and isinstance(actual, TypeConstructor):
        if pattern.name != actual.name or len(pattern.args) != len(actual.args):
            return None
        for left, right in zip(pattern.args, actual.args):
            found = _type_argument(left, right, variable)
            if found is not None:
                return found
    return None


def _int_measure(ctx: TypingContext, fun: Name, argument: Term, argument_type: Type) -> Term | None:
    """Apply an in-scope measure whose liquid form is ``fun(argument)``."""
    schema = ctx.type_of(fun)
    if schema is None:
        return None
    head: Term = Var(fun)
    current = schema
    while isinstance(current, TypePolymorphism):
        body = current.body
        while isinstance(body, (TypePolymorphism, RefinementPolymorphism)):
            body = body.body
        if not isinstance(body, AbstractionType):
            return None
        instance = _type_argument(body.var_type, argument_type, current.name)
        if instance is None:
            return None
        head = TypeApplication(head, instance)
        current = type_substitution(current.body, current.name, instance)
    if isinstance(current, RefinementPolymorphism) or not isinstance(current, AbstractionType):
        return None
    if not shapes_match(argument_type, current.var_type) or base_type_of(current.type) != t_int:
        return None
    return Application(head, argument)


def _int_operand(ctx: TypingContext, liquid: LiquidTerm) -> Term | None:
    if isinstance(liquid, LiquidLiteralInt):
        return Literal(liquid.value, t_int)
    if isinstance(liquid, LiquidVar):
        ty = ctx.type_of(liquid.name)
        if ty is not None and base_type_of(ty) == t_int:
            return Var(liquid.name)
        return None
    if isinstance(liquid, LiquidApp) and liquid.fun == Name("+", 0) and len(liquid.args) == 2:
        left, right = _int_operand(ctx, liquid.args[0]), _int_operand(ctx, liquid.args[1])
        if left is None or right is None:
            return None
        return Application(Application(TypeApplication(Var(Name("+", 0)), t_int), left), right)
    if isinstance(liquid, LiquidApp) and len(liquid.args) == 1 and isinstance(liquid.args[0], LiquidVar):
        argument_type = ctx.type_of(liquid.args[0].name)
        if argument_type is None:
            return None
        return _int_measure(ctx, liquid.fun, Var(liquid.args[0].name), argument_type)
    return None


def _compile_guard(ctx: TypingContext, guard: LiquidTerm) -> Term | None:
    """Boolean program for a guard ``abduce`` solved but did not realize.

    ``realize`` covers variables and ``⋆ op ⋆`` over scalars. A measure
    application such as ``len xs = 0`` is already the abducted condition; it
    is not a second search for an ``if`` condition.
    """
    from aeon.synthesis.modules.synquid.qualifiers import realize

    realized = realize(ctx, guard)
    if realized is not None:
        return realized
    if isinstance(guard, LiquidApp) and guard.fun in _RELATIONS and len(guard.args) == 2:
        left, right = _int_operand(ctx, guard.args[0]), _int_operand(ctx, guard.args[1])
        if left is None or right is None:
            return None
        return Application(Application(TypeApplication(Var(guard.fun), t_int), left), right)
    if isinstance(guard, LiquidApp) and guard.fun in (Name("&&", 0), Name("||", 0)) and len(guard.args) == 2:
        left, right = _compile_guard(ctx, guard.args[0]), _compile_guard(ctx, guard.args[1])
        if left is None or right is None:
            return None
        return Application(Application(Var(guard.fun), left), right)
    if isinstance(guard, LiquidApp) and guard.fun == Name("!", 0) and guard.args:
        inner = _compile_guard(ctx, guard.args[0])
        if inner is None:
            return None
        return Application(Var(guard.fun), inner)
    return None


def _then_arms(hole: TypedHole, skip: Callable[[Name], bool]) -> Iterator[Term]:
    """Complete leaf and depth-1 eliminations already built by TDSyn."""
    for term, holes in backward_close_candidates(hole, skip):
        if not holes:
            yield term
    for term, holes in backward_lit_candidates(hole, skip):
        if not holes:
            yield term
    for term, holes, _ in _iter_forward_applications(hole, skip):
        if not holes:
            yield term


def abduced_if_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """One complete then-arm, its abducted guard, and an else hole under the negation.

    Unrefined goals stay on ``backward_if_candidates``. This production is only
    for a refined goal, where copying the goal onto ``?c``, ``?t`` and ``?e``
    does not determine the guard.
    """
    if not _refined_goal(hole) or monotonic() >= deadline.get():
        return []
    from aeon.synthesis.modules.synquid.abduction import abduce, branch_environment
    from aeon.synthesis.modules.synquid.constraints import ConstraintState
    from aeon.synthesis.modules.synquid.solver import Status

    goal = hole.expected_type
    arms = _then_arms(hole, skip)
    first = next(arms, None)
    if first is None:
        return []
    # Guard inference is one optional production, not the entire search. Pass
    # the outer deadline through to Synquid and leave time for other tactics.
    state = ConstraintState(hole.context, deadline=min(deadline.get(), monotonic() + _ABDUCTION_SECONDS))
    # Same split as Synquid's generateThen: open the unknown path condition,
    # then solve the guard against the parent state from one finished arm.
    try:
        opened = branch_environment(state, goal)
        if opened.inhabited() == Status.VALID:
            return []
    except Exception:
        return []
    found: list[tuple[Term, list[TypedHole]]] = []
    seen: set[str] = set()
    attempts = 0
    for arm in chain((first,), arms):
        if attempts >= _ABDUCTION_ATTEMPTS or monotonic() >= state.deadline:
            break
        key = repr(arm)
        if key in seen:
            continue
        seen.add(key)
        attempts += 1
        try:
            result = abduce(state, arm, goal)
        except Exception:
            continue
        guards = list(result.guards)
        if not guards:
            for condition in result.conditions:
                program = _compile_guard(hole.context, condition)
                if program is not None:
                    guards.append((condition, program))
                    break
        if not guards:
            continue
        _condition, guard = guards[0]
        else_term, else_hole = fresh_hole(goal, hole.context, domain=hole.domain)
        # ``scoped_children`` records the negated guard when this if is installed.
        found.append((If(guard, arm, else_term, _loc), [else_hole]))
        break
    return found


def _scrutinee_eliminators(
    hole: TypedHole,
    applications: list[tuple[Term, list[TypedHole]]],
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Apply ``T_rec`` to one in-scope scrutinee and leave the handlers open.

    The eliminator is an ordinary application. Filling the scrutinee up front
    keeps a refined datatype goal from enumerating every list producer before
    the match that the goal actually needs.
    """
    if not _refined_goal(hole):
        return []
    for term, holes in applications:
        if not is_eliminator_term(term) or not holes:
            continue
        scrutinee = holes[0]
        for var_name, var_type in iter_concrete_vars(hole.context, skip, hole.domain):
            if not shapes_match(var_type, scrutinee.expected_type):
                continue
            filled = substitute_holes_map(term, {scrutinee.name: Var(var_name)})
            rest = holes[1:]
            if candidate_feasible(hole, filled, rest):
                return [(filled, rest)]
    return []


def _liquid_decreases(term: LiquidTerm) -> bool:
    if isinstance(term, LiquidApp):
        return term.fun.name == "<" or any(_liquid_decreases(arg) for arg in term.args)
    return False


def _type_decreases(ty: Type) -> bool:
    """True when a hypothesis carries the strict metric from ``weaken``."""
    if isinstance(ty, RefinedType):
        return _liquid_decreases(ty.refinement) or _type_decreases(ty.type)
    if isinstance(ty, AbstractionType):
        return _type_decreases(ty.var_type) or _type_decreases(ty.type)
    if isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
        return _type_decreases(ty.body)
    return False


def _vars_matching(
    variables: list[tuple[Name, Type]],
    target: Type,
) -> list[tuple[Name, Type]]:
    return [(name, ty) for name, ty in variables if shapes_match(ty, target)]


def _apply_variables(
    fun: Term,
    ty: Type,
    variables: list[tuple[Name, Type]],
    datatype: Type,
    *,
    limit: int,
) -> list[Term]:
    """Fully apply ``fun``, using the most recently bound datatype variable first.

    That variable is the case tail. Later datatype arguments are the other
    lists in scope (``ys`` before the scrutinee, once the tail is used).
    """
    found: list[Term] = []

    def walk(term: Term, current: Type, prefer_recent: bool, used: set[Name]) -> None:
        if len(found) >= limit:
            return
        if not isinstance(current, AbstractionType):
            found.append(term)
            return
        matches = _vars_matching(variables, current.var_type)
        if not matches:
            return
        datatype_slot = shapes_match(current.var_type, datatype)
        ordered = list(reversed(matches)) if prefer_recent and datatype_slot else matches
        for name, _var_type in ordered:
            if datatype_slot and name in used:
                continue
            arg = Var(name, _loc)
            walk(
                Application(term, arg, _loc),
                substitution_in_type(current.type, arg, current.var_name),
                False,
                used | {name},
            )
            if len(found) >= limit:
                return

    walk(fun, ty, True, set())
    return found


def _apply_constructor(
    fun: Term,
    ty: Type,
    recursive_terms: list[Term],
    variables: list[tuple[Name, Type]],
    datatype: Type,
    *,
    limit: int,
) -> list[Term]:
    """Fill one recursive constructor slot with a decreasing call and the rest with variables."""
    found: list[Term] = []

    def walk(term: Term, current: Type, recursive_open: bool) -> None:
        if len(found) >= limit:
            return
        if not isinstance(current, AbstractionType):
            if not recursive_open:
                found.append(term)
            return
        if recursive_open and shapes_match(current.var_type, datatype):
            for recursive in recursive_terms:
                walk(
                    Application(term, recursive, _loc),
                    substitution_in_type(current.type, recursive, current.var_name),
                    False,
                )
                if len(found) >= limit:
                    return
            return
        for name, _var_type in _vars_matching(variables, current.var_type):
            arg = Var(name, _loc)
            walk(
                Application(term, arg, _loc),
                substitution_in_type(current.type, arg, current.var_name),
                recursive_open,
            )
            if len(found) >= limit:
                return

    walk(fun, ty, True)
    return found


def recursive_fold_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """``cons h (recursive t ys)`` from the weakened hypothesis and one constructor.

    The case binders are in scope only under the handler, so the nil branch
    does not see this production. The root goal has no element variable and
    does not see it either; the scrutinee eliminator stays the first match.
    """
    datatype = base_type_of(hole.expected_type)
    if datatype is None or datatype in (t_int, t_bool, t_float, t_string) or hole.domain is not ExpressionDomain.TERM:
        return []
    library = get_component_library(hole.context, skip, hole.nonterminal)
    functions = library.functions_returning(hole.expected_type)
    decreasing = [
        (term, ty)
        for term, ty in functions
        if _type_decreases(ty) and not is_constructor_term(term) and not is_eliminator_term(term)
    ]
    constructors = [(term, ty) for term, ty in functions if is_constructor_term(term)]
    if not decreasing or not constructors:
        return []
    variables = list(iter_concrete_vars(hole.context, skip, hole.domain))
    found: list[tuple[Term, list[TypedHole]]] = []
    seen: set[str] = set()
    for cons_term, cons_ty in constructors:
        for dec_term, dec_ty in decreasing:
            calls = _apply_variables(dec_term, dec_ty, variables, datatype, limit=4)
            if not calls:
                continue
            for term in _apply_constructor(cons_term, cons_ty, calls, variables, datatype, limit=8 - len(found)):
                key = repr(term)
                if key in seen:
                    continue
                seen.add(key)
                if candidate_feasible(hole, term, []):
                    found.append((term, []))
                if len(found) >= 8:
                    return found
    return found


def backward_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Backward action: from expected type, find terms that produce a subtype.

    Combines the granular backward tactics. Given hole expecting type T:
    1. If T is a function type, produce an abstraction (and nothing else)
    2. Generate literals for base types
    3. Look up variables with matching types
    4. For a refined goal, abduce one guard from a complete then-arm
    5. Find functions whose return type matches T
    6. If abduction supplies no branch, generate an ordinary if-then-else
    """
    abs_candidates = backward_abs_candidates(hole, skip)
    if abs_candidates:
        return abs_candidates  # For function types, only produce abstractions

    candidates: list[tuple[Term, list[TypedHole]]] = []
    # Applications are computed before the other slices only for a refined
    # goal, which needs them to fill one scrutinee. An unrefined goal keeps
    # the historical slice order: literals, variables, applications, if.
    applications: list[tuple[Term, list[TypedHole]]] | None = None
    if _refined_goal(hole):
        applications = backward_app_candidates(hole, skip)
        candidates.extend(_scrutinee_eliminators(hole, applications, skip))
    # A case handler with the weakened hypothesis closes as one constructor
    # around one decreasing call. No element variable, no candidate.
    candidates.extend(recursive_fold_candidates(hole, skip))
    candidates.extend(backward_lit_candidates(hole, skip))
    candidates.extend(backward_close_candidates(hole, skip))
    # Prefer a guard inferred from a finished then-arm. Keep the ordinary
    # three-hole conditional when inference is inapplicable or inconclusive.
    branches = abduced_if_candidates(hole, skip) if _refined_goal(hole) else []
    candidates.extend(branches)
    if applications is None:
        applications = backward_app_candidates(hole, skip)
    candidates.extend(applications)
    if not branches:
        candidates.extend(backward_if_candidates(hole, skip))
    return candidates


def iter_backward_candidates(
    hole: TypedHole, skip: Callable[[Name], bool], rng: Random | None = None, *, constructors_only: bool = False
) -> Iterator[Candidate]:
    if constructors_only:
        actions = [
            iter_forward_close_candidates(hole, skip, rng, constructors_only=True),
            iter_backward_app_candidates(hole, skip, rng, constructors_only=True),
        ]
        for candidates in _ordered(actions, rng):
            yield from candidates
        return
    abstractions = backward_abs_candidates(hole, skip)
    if abstractions:
        yield from abstractions
        return
    folds = recursive_fold_candidates(hole, skip)
    if folds:
        yield from folds
    leaves = [
        iter_backward_lit_candidates(hole, skip, rng),
        iter_forward_close_candidates(hole, skip, rng),
    ]
    applications = iter_backward_app_candidates(hole, skip, rng)

    def branches():
        inferred = abduced_if_candidates(hole, skip) if _refined_goal(hole) else []
        yield from inferred or backward_if_candidates(hole, skip)

    # Creating the iterator must not perform Horn inference before the
    # consumer has even seen a literal, variable or constructor application.
    actions = [*leaves, applications, branches()]
    for candidates in _ordered(actions, rng):
        yield from candidates


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
    ``let v := f(x, ...) in ?goal`` candidate. Check the bound value against
    the goal contract, which is already well-scoped at the binding site.
    Extracted return types can mention unopened formals even inside datatype
    parameters; shallow refinement erasure does not close them.
    """
    if hole.domain is ExpressionDomain.REFINEMENT:
        return []
    return [
        _let_candidate(hole, value_term, value_holes, hole.expected_type)
        for value_term, value_holes, _ in _forward_applications(hole, skip)
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
        for value_term, mono_type in monomorphize(name, var_type, ctx, hole.expected_type):
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
