"""Round-trip application search and branch-first liquid condition abduction."""

from __future__ import annotations

from itertools import count, takewhile, islice
from time import monotonic
from typing import Callable

from aeon.synthesis.grammar.nonterminals import grammar_bindings
from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidLiteralBool, liquid_free_vars
from aeon.core.substitutions import substitution, instantiate_refinement_with_horn_in_type
from aeon.core.terms import (
    Annotation,
    Application,
    If,
    Literal,
    Term,
    TypeApplication,
    Var,
    RefinementApplication,
    ImplicitRefinementHole,
)
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    RefinementPolymorphism,
)
from aeon.compilation.session import current_session
from aeon.prelude.prelude import ALL_OPS
from aeon.synthesis.modules.synquid.decompose import uncurry as uncurry
from aeon.synthesis.modules.synquid.constraints import ConstraintState, negate, fresh_name
from aeon.synthesis.modules.synquid.round_trip import ApplicationState, erase, match_result
from aeon.synthesis.modules.synquid.solver import SearchStats, SMTQueryState, Status
from aeon.synthesis.modules.synquid.abduction import abduce, branch_environment
from aeon.typechecking.context import (
    RefinementBinder,
    ReflectedBinder,
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.utils.name import Name
from aeon.verification.state import VerificationState

# Arithmetic, comparison, and Boolean operators are scalar components. ``toFloat``
# is the one prelude coercion outside ``ALL_OPS`` with the same restriction.
_PRELUDE_OPERATORS = frozenset(ALL_OPS) | {"toFloat"}
_SCALAR_BASES = frozenset({"Int", "Bool", "Float", "String"})
_NEGATIVE_CACHE_LIMIT = 4096


def monomorfic(t: Type, typing_ctx: TypingContext, t_l: dict[Name, Type]):
    match t:
        case TypePolymorphism(var_name, _, var_body):
            for t in [
                t
                for n, t in grammar_bindings(typing_ctx)
                if isinstance(t, TypeConstructor) and t != TypeConstructor(Name("Unit", 0))
            ]:
                t_l[var_name] = t
                for result in monomorfic(var_body, typing_ctx, t_l):
                    yield result
        case AbstractionType(var_name, var_type, typ):
            for in_type in monomorfic(var_type, typing_ctx, t_l):
                for body in monomorfic(typ, typing_ctx, t_l):
                    yield AbstractionType(var_name, in_type, body)
        case TypeVar(var_name):
            yield t_l[var_name]
        case _:
            yield t


def frange(start, stop, step):
    return takewhile(lambda x: x < stop, count(start, step))


def _solve_literal(ret_t: Type, base_t: TypeConstructor, deadline=float("inf")):
    """Propose one SMT model literal; final checking still proves the goal.

    Free context variables are existential in this proposal query. A chosen
    literal is not thereby proved valid for every value of those variables.
    """
    from z3 import Solver, sat

    from aeon.verification.smt import make_variable, translate_liq

    if monotonic() >= deadline:
        return

    if isinstance(ret_t, RefinedType):
        binder, refinement = ret_t.name, ret_t.refinement
    else:
        binder, refinement = Name("_lit", 0), LiquidLiteralBool(True)

    # The binder is the unknown to solve for; any other free variables in the VC
    # are unknown context values, given fresh consts so the binder is solved
    # relative to them.
    variables: dict[str, object] = {str(binder): make_variable(str(binder), base_t)}
    for fv in liquid_free_vars(refinement):
        variables.setdefault(str(fv), make_variable(str(fv), base_t))

    try:
        s = Solver()
        s.set(timeout=max(1, int((deadline - monotonic()) * 1000)) if deadline != float("inf") else 0)
        s.add(translate_liq(refinement, variables))
        if s.check() != sat:
            return
        model_val = s.model()[variables[str(binder)]]
    except Exception:
        return

    if base_t.name.name == "Int":
        yield Literal(0 if model_val is None else model_val.as_long(), base_t)
    else:  # Float
        yield Literal(0.0 if model_val is None else float(model_val.as_fraction()), base_t)


def _local_check(ctx: TypingContext, term: Term, goal: Type, state: ConstraintState | None = None) -> bool:
    """Discharge a construction rule's obligation before emitting its term."""
    from aeon.typechecking.typeinfer import check

    trial = state.fork() if state is not None else ConstraintState(ctx)
    try:
        trial.add(check(trial.context, term, goal))
        return trial.solve() == Status.VALID
    except Exception:
        return False


def _arg_gen(ctx, level, goal, skip, mem, state):
    unknowns = state.unresolved(goal)
    if unknowns:
        from aeon.synthesis.modules.synquid.inference import infer_terms

        yield from infer_terms(ctx, max(0, level - 1), skip, mem, state)
        return
    depth = level - 1 if isinstance(erase(goal), (TypeConstructor, AbstractionType)) else 0
    yield from synthes_memory(
        ctx, max(0, depth), goal, skip, mem, state, conditionals=isinstance(erase(goal), AbstractionType)
    )


def _application_terms(ctx, level, head, application, skip, mem, filling=False):
    if monotonic() >= mem.get("synquid_deadline", float("inf")):
        return
    status = application.check()
    if status in (Status.INVALID, Status.EXHAUSTED):
        if application.params:
            application.state.stats.partial_rejections += 1
        else:
            application.state.stats.complete_rejections += 1
        return
    if not application.params:
        if application.deferred:
            deferred = ApplicationState(
                application.state.fork(), application.deferred, application.result, application.goal
            )
            yield from _application_terms(ctx, level, head, deferred, skip, mem, filling=True)
        else:
            if application.state.finalize() != Status.VALID:
                return
            for assignment in application.state.assignments:
                yield _materialize_term(head, assignment, application.state)
        return
    binder, expected = application.params[0]
    if isinstance(expected, AbstractionType) and len(application.params) > 1 and not filling:
        # APPHO: infer first-order facts before constructing the anonymous
        # function. Its value is not a scalar and cannot occur in the result.
        deferred = ApplicationState(
            application.state.fork(),
            application.params[1:],
            application.result,
            application.goal,
            application.deferred + [(binder, expected)],
        )
        yield from _application_terms(ctx, level, Application(head, Var(binder)), deferred, skip, mem)
        return
    _, expected = application.params[0]
    seen = set()
    for assignment in application.state.assignments:
        goal = application.state.materialize(expected, assignment)
        for argument in _arg_gen(ctx, level, goal, skip, mem, application.state):
            key = repr(argument)
            if key in seen:
                continue
            seen.add(key)
            application.state.stats.argument_candidates += 1
            try:
                child = application.choose(argument)
            except ValueError:
                application.state.stats.partial_rejections += 1
                continue
            except Exception:
                application.state.stats.record(Status.UNSUPPORTED)
                # No later whole-program oracle repairs missing argument
                # evidence. An unsupported construction cannot certify a term.
                continue
            from aeon.synthesis.modules.synquid.inference import InferredArgument

            argument = argument.term if isinstance(argument, InferredArgument) else argument
            new_head = substitution(head, argument, binder) if filling else Application(head, argument)
            yield from _application_terms(ctx, level, new_head, child, skip, mem, filling)


def _materialize_term(term, assignment, state):
    from dataclasses import replace
    from aeon.core.terms import Abstraction, TypeAbstraction, RefinementAbstraction, Let, Rec

    if isinstance(term, TypeApplication):
        return TypeApplication(
            _materialize_term(term.body, assignment, state), state.materialize(term.type, assignment)
        )
    if isinstance(term, RefinementApplication):
        argument = term.refinement
        if isinstance(argument, ImplicitRefinementHole) and argument.name in state.predicates:
            argument = state.materialize_predicate(argument.name, assignment)
        return RefinementApplication(_materialize_term(term.body, assignment, state), argument)
    if isinstance(term, Application):
        return Application(
            _materialize_term(term.fun, assignment, state), _materialize_term(term.arg, assignment, state)
        )
    if isinstance(term, Annotation):
        return Annotation(_materialize_term(term.expr, assignment, state), state.materialize(term.type, assignment))
    if isinstance(term, (Abstraction, TypeAbstraction, RefinementAbstraction)):
        return replace(term, body=_materialize_term(term.body, assignment, state))
    if isinstance(term, If):
        return replace(
            term,
            cond=_materialize_term(term.cond, assignment, state),
            then=_materialize_term(term.then, assignment, state),
            otherwise=_materialize_term(term.otherwise, assignment, state),
        )
    if isinstance(term, (Let, Rec)):
        updates = dict(
            var_value=_materialize_term(term.var_value, assignment, state),
            body=_materialize_term(term.body, assignment, state),
        )
        if isinstance(term, Rec):
            updates["var_type"] = state.materialize(term.var_type, assignment)
        return replace(term, **updates)
    return term


def _peel_polymorphism(ty: Type) -> tuple[list[Name], Type]:
    """Strip the ``forall`` prefix, returning the bound type variables and body."""
    tyvars: list[Name] = []
    cur = ty
    while isinstance(cur, (TypePolymorphism, RefinementPolymorphism)):
        if isinstance(cur, TypePolymorphism):
            tyvars.append(cur.name)
        cur = cur.body
    return tyvars, cur


def _uncurry_arrow_b(ty: Type) -> tuple[list[tuple[Name, Type]], Type]:
    """Split an arrow type into ``(binder, argument-type)`` pairs and the return
    type, tolerating type-variable domains (e.g. ``(hd: a) -> (tl: List a) ->
    List a``) -- which arise before a polymorphic binding is instantiated, and
    which ``uncurry`` rejects. The binder names let a chosen argument be
    substituted into the dependent parameter types that follow it (incremental
    unification)."""
    params: list[tuple[Name, Type]] = []
    cur = ty
    while isinstance(cur, AbstractionType):
        params.append((cur.var_name, cur.var_type))
        cur = cur.type
    return params, cur


def closing(elems: tuple, typ: TypeConstructor):
    if len(elems) == 1:
        return TypeApplication(elems[0], typ)
    else:
        return Application(closing(elems[:-1], typ), elems[-1])


def _scalar_base_name(ty: Type) -> str | None:
    base = erase(ty)
    if isinstance(base, TypeConstructor) and not base.args:
        return base.name.name
    return None


def _skip_prelude_operator(name: Name, goal: Type) -> bool:
    """Prelude operators stay on Int, Bool, Float, and String goals.

    Their schemas are polymorphic (``forall a. a -> a -> a``), so a datatype
    goal would otherwise treat ``+`` as a list producer.
    """
    return name.name in _PRELUDE_OPERATORS and _scalar_base_name(goal) not in _SCALAR_BASES


class _NegativeCache:
    """Definite failed subgoals for one compilation session.

    Successful terms are not stored. A key has to mention the pending liquid
    state, so a positive hit would still need to materialize that assignment.
    """

    def __init__(self) -> None:
        self.entries: set[tuple[object, ...]] = set()
        self.session: object = None
        self.generation = -1

    def prepare(self) -> None:
        session = current_session()
        generation = session.state(VerificationState).generation
        if self.session is not session or self.generation != generation:
            self.entries.clear()
            self.session = session
            self.generation = generation


def _negative_cache(mem: dict) -> _NegativeCache:
    cache = mem.get("synquid_negative_cache")
    if not isinstance(cache, _NegativeCache):
        cache = _NegativeCache()
        mem["synquid_negative_cache"] = cache
    cache.prepare()
    return cache


def _context_entry_key(entry: object) -> tuple[str, str] | None:
    """A stable identity for one context entry in a negative-cache key."""
    if isinstance(entry, (VariableBinder, RefinementBinder, UninterpretedBinder, ReflectedBinder)):
        return str(entry.name), repr(entry.type)
    if isinstance(entry, TypeConstructorBinder):
        return str(entry.name), repr(tuple(entry.args))
    if isinstance(entry, TypeBinder):
        return str(entry.type_name), repr(entry.type_kind)
    return None


def _negative_key(
    level: int,
    goal: Type,
    state: ConstraintState,
    conditionals: bool,
    skip: Callable[[Name], bool],
    mem: dict,
) -> tuple[object, ...]:
    """Everything a subgoal consults, except a liquid assignment of a success.

    Path assumptions live in the context. Pending obligations are the unsolved
    constraints. Fresh predicate names distinguish forks that invented different
    unknowns. ``id(skip)`` keeps a recursive hypothesis from sharing a failure
    recorded while that hypothesis was hidden.
    """
    binders = tuple(key for entry in state.context.entries if (key := _context_entry_key(entry)) is not None)
    return (
        level,
        conditionals,
        state.match_depth,
        mem.get("synquid_match_depth"),
        mem.get("synquid_fix", True),
        repr(goal),
        repr(state.pending),
        repr(state.constraints),
        tuple(sorted(str(name) for name in state.matched)),
        binders,
        tuple(sorted((str(name), repr(ty)) for name, ty in state.type_assignments.items())),
        tuple(sorted(str(name) for name in state.predicates)),
        id(skip),
    )


def _definite_failure(before: dict[str, int], after: dict[str, int]) -> bool:
    """True when every new solver answer was INVALID or EXHAUSTED."""
    if after.get(Status.UNKNOWN.value, 0) > before.get(Status.UNKNOWN.value, 0):
        return False
    if after.get(Status.UNSUPPORTED.value, 0) > before.get(Status.UNSUPPORTED.value, 0):
        return False
    invalid = after.get(Status.INVALID.value, 0) - before.get(Status.INVALID.value, 0)
    exhausted = after.get(Status.EXHAUSTED.value, 0) - before.get(Status.EXHAUSTED.value, 0)
    return invalid > 0 or exhausted > 0


def synthes_memory(
    ctx: TypingContext,
    level: int,
    ret_t: Type,
    skip: Callable[[Name], bool],
    mem: dict,
    state: ConstraintState | None = None,
    *,
    conditionals: bool = True,
):
    # Positive term memoization stays off: a hit would have to replay the liquid
    # assignment that built the term. Failed subgoals are cached only when every
    # solver answer was a definite invalid or exhausted result.
    if state is None:
        state = ConstraintState(
            ctx,
            stats=mem.setdefault("synquid_stats", SearchStats()),
            deadline=mem.get("synquid_deadline", float("inf")),
            solver_state=mem.setdefault("synquid_solver_state", SMTQueryState()),
        )
    deadline = mem.get("synquid_deadline", float("inf"))
    if monotonic() >= deadline:
        return
    cache = _negative_cache(mem)
    try:
        key = _negative_key(level, ret_t, state, conditionals, skip, mem)
    except Exception:
        key = None
    if key is not None and key in cache.entries:
        return
    before = dict(state.stats.outcomes)
    found = False
    try:
        for item in synthes(ctx, level, ret_t, skip, mem, state, conditionals=conditionals):
            if monotonic() >= deadline:
                return
            found = True
            yield item
    except NotImplementedError:
        return
    if found or key is None or monotonic() >= deadline:
        return
    if not _definite_failure(before, state.stats.outcomes):
        return
    if len(cache.entries) < _NEGATIVE_CACHE_LIMIT:
        cache.entries.add(key)


def match_type(t1: Type, t2: Type):
    if t1 == t2:
        return True
    elif type(t1) is type(t2):
        return False
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        return match_type(t1.var_type, t2.var_type) and match_type(t1.type, t2.type)
    else:
        return False


def _leaf_terms(ctx, ret_t, skip, state):
    for term in _leaf_proposals(ctx, ret_t, skip, state.deadline):
        if _local_check(ctx, term, ret_t, state):
            yield term


def _leaf_proposals(ctx, ret_t, skip, deadline):
    base_t = erase(ret_t)
    arrow_goal: AbstractionType | None = ret_t if isinstance(ret_t, AbstractionType) else None
    if arrow_goal is None and isinstance(ret_t, RefinedType) and isinstance(ret_t.type, AbstractionType):
        arrow_goal = ret_t.type
    if arrow_goal is not None:
        for name, _ in [
            (n, t)
            for n, t in grammar_bindings(ctx)
            if isinstance(t, AbstractionType) and match_result(t, arrow_goal, set()) is not None and not skip(n)
        ]:
            yield Var(name)
        return
    if isinstance(base_t, TypeVar):
        for name, t in grammar_bindings(ctx):
            if erase(t) == base_t and not skip(name):
                yield Var(name)
        return
    assert isinstance(base_t, TypeConstructor)
    for name, _ in [
        (n, t)
        for n, t in grammar_bindings(ctx)
        if isinstance(t, (TypeConstructor, RefinedType)) and erase(t) == base_t and not skip(n)
    ]:
        yield Var(name)
    match base_t:
        case TypeConstructor(Name("Bool", 0)):
            yield from [Literal(True, base_t), Literal(False, base_t)]
        case TypeConstructor(Name("Int", 0)):
            # ?intLit: solved by z3 against the VC (goal refinement) here.
            yield from dict.fromkeys([*_solve_literal(ret_t, base_t, deadline), Literal(0, base_t), Literal(1, base_t)])
        case TypeConstructor(Name("Float", 0)):
            # ?floatLit: solved by z3 against the VC (goal refinement) here.
            yield from _solve_literal(ret_t, base_t, deadline)
        case TypeConstructor(Name("String", 0)):
            yield from (
                Literal(s, base_t)
                for s in ("", " ", "a", "b", "0", "1", "x", "y", "\n", "\t", "true", "false", "[]", "{}", "nil")
            )
        case TypeConstructor(Name("Unit", 0)):
            yield Literal(None, base_t)
        case _:
            return


def _eliminations(
    ctx: TypingContext,
    level: int,
    ret_t: Type,
    skip: Callable[[Name], bool],
    mem: dict,
    state: ConstraintState | None = None,
    *,
    conditionals: bool = True,
):
    if state is None:
        state = ConstraintState(
            ctx,
            stats=mem.setdefault("synquid_stats", SearchStats()),
            deadline=mem.get("synquid_deadline", float("inf")),
        )
    if level == 0:
        yield from _leaf_terms(ctx, ret_t, skip, state)
    for name, typ in [
        (n, ty) for n, ty in grammar_bindings(ctx) if not isinstance(ty, (TypeConstructor, RefinedType)) and not skip(n)
    ]:
        from aeon.verification.constructor_registry import get_constructor_groups

        if name.name.endswith("_rec") and name.name[:-4] in get_constructor_groups():
            continue
        if monotonic() >= mem.get("synquid_deadline", float("inf")):
            return
        branch_state = state.fork()
        tyvars, inner = _peel_polymorphism(typ)
        params, result = _uncurry_arrow_b(inner)
        if level == 0 and params:
            continue
        shape = match_result(result, ret_t, set(tyvars))
        if shape is None:
            continue
        if _skip_prelude_operator(name, ret_t):
            continue
        head: Term = Var(name)
        atoms = extract_qualifier_atoms(ctx, goal_type=ret_t, max_atoms=None)
        inner = typ
        while isinstance(inner, (TypePolymorphism, RefinementPolymorphism)):
            if isinstance(inner, TypePolymorphism):
                tv = inner.name
                if tv in shape:
                    instance = branch_state.fresh_type(shape[tv], atoms)
                else:
                    instance = branch_state.fresh_variable(inner.kind)
                inner = type_substitution(inner.body, tv, instance)
                head = TypeApplication(head, instance)
            else:
                from aeon.core.substitutions import instantiate_refinement_in_type
                from aeon.synthesis.grammar.poly import predicate_argument
                from aeon.synthesis.modules.tdsyn.helpers import result_predicate

                retained = result_predicate(inner.body, inner.name, inner.sort, ret_t)
                if retained is not None:
                    head = RefinementApplication(head, predicate_argument(ctx, retained, inner.sort))
                    inner = instantiate_refinement_in_type(inner.body, inner.name, retained)
                else:
                    predicate = branch_state.refinement_parameter(inner.sort)
                    inner = instantiate_refinement_with_horn_in_type(inner.body, inner.name, inner.sort, predicate.name)
                    head = RefinementApplication(head, ImplicitRefinementHole(predicate.name))
        application = ApplicationState.start(branch_state, inner, ret_t)
        yield from _application_terms(ctx, level, head, application, skip, mem)


def synthes(ctx, level, ret_t, skip, mem, state=None, *, conditionals=True):
    """Section 3.7, following ``generateMaybeMatchIf``.

    Outside a match: depth-0 E-terms, then the match unknown, then
    applications and IFAB. Aeon's solver cannot discharge a datatype
    equation, so the structural match stands in for that unknown and its
    cases use a full application bound. Inside a match arm, applications
    come before another match. Computed scrutinees are the final fallback
    and cost one application. The other conditional branch keeps ``level``.
    """
    from aeon.synthesis.modules.synquid.functions import function_terms
    from aeon.synthesis.modules.synquid.patterns import abduced_matches, match_terms, match_variables
    from aeon.core.liquid import LiquidApp, LiquidVar
    from aeon.core.types import t_bool

    if state is None:
        state = ConstraintState(
            ctx,
            stats=mem.setdefault("synquid_stats", SearchStats()),
            deadline=mem.get("synquid_deadline", float("inf")),
        )
    if isinstance(ret_t, (TypePolymorphism, RefinementPolymorphism, AbstractionType)):
        yield from function_terms(ctx, level, ret_t, skip, mem, state)
        return

    def leaves(branch):
        yield from _eliminations(ctx, 0, ret_t, skip, mem, branch, conditionals=False)

    def deeper(branch):
        if level > 0:
            yield from _eliminations(ctx, level, ret_t, skip, mem, branch, conditionals=False)

    def expressions(branch):
        yield from leaves(branch)
        yield from deeper(branch)

    if not conditionals:
        # Scrutinee and argument generation stay elimination-only. Matching
        # here would synthesize a scrutinee by matching again.
        yield from expressions(state)
        return
    # A depth-0 E-term with a true condition is returned as itself.
    for term in leaves(state):
        if _local_check(ctx, term, ret_t, state):
            yield term
    # Outside a match, the match unknown is tried before applications and
    # before the full conditional qualifier set. Aeon's Horn theory does not
    # solve datatype equations, so the structural match is that unknown.
    # Inside an arm, applications come first: the cons case is a recursive
    # call, and another match is only the fallback.
    if state.match_depth == 0:
        yield from abduced_matches(ctx, level, ret_t, skip, mem, state)
        yield from match_variables(ctx, level, ret_t, skip, mem, state)
    for term in deeper(state):
        if _local_check(ctx, term, ret_t, state):
            yield term
    if state.match_depth > 0:
        yield from abduced_matches(ctx, level, ret_t, skip, mem, state)
        yield from match_variables(ctx, level, ret_t, skip, mem, state)
    # IFAB is the path-condition unknown. It runs at this depth for every goal.
    proposals = expressions(branch_environment(state, ret_t))
    for then in islice(proposals, 64):
        if monotonic() >= state.deadline:
            return
        result = abduce(state, then, ret_t)
        if result.status in (Status.UNKNOWN, Status.UNSUPPORTED) and _local_check(ctx, then, ret_t, state):
            # Unsupported local logic remains eligible for whole-program
            # verification; it cannot justify pruning an otherwise valid term.
            yield then
        guards = dict(result.guards)
        for condition in result.conditions:
            otherwise_state = state.assume(negate(condition))
            if otherwise_state.inhabited() == Status.VALID:
                if _local_check(ctx, then, ret_t, state):
                    yield then
                continue
            # Both regions must be demonstrably nonempty. In particular, an
            # unknown SMT answer cannot authorize recursive IFAB expansion.
            if otherwise_state.inhabited() != Status.INVALID or state.assume(condition).inhabited() != Status.INVALID:
                continue
            binder = fresh_name("guard")
            guard_type = RefinedType(binder, t_bool, LiquidApp(Name("==", 0), [LiquidVar(binder), condition]))
            if condition in guards:
                guard_terms = [guards[condition]]
            else:
                guard_terms = synthes_memory(ctx, level, guard_type, skip, mem, state, conditionals=False)
            for guard in guard_terms:
                if not _local_check(ctx, guard, guard_type, state):
                    continue
                state.stats.abduced_guards += 1
                for otherwise in synthes_memory(ctx, level, ret_t, skip, mem, otherwise_state):
                    if _local_check(ctx, otherwise, ret_t, otherwise_state):
                        yield Annotation(If(guard, then, otherwise), ret_t)
    # Computed scrutinees are generateMatch after variable scrutinees, and
    # they cost one application.
    if level > 0:
        yield from match_terms(ctx, level, ret_t, skip, mem, state)
