"""Round-trip application search and branch-first liquid condition abduction."""

from __future__ import annotations

from itertools import chain, count, takewhile, islice
from time import monotonic
from typing import Callable

from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidLiteralBool, liquid_free_vars
from aeon.core.substitutions import substitution, substitution_in_type, instantiate_refinement_with_horn_in_type
from aeon.core.terms import (
    Abstraction,
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
from aeon.synthesis.modules.synquid.decompose import uncurry as uncurry
from aeon.synthesis.modules.synquid.constraints import ConstraintState, negate, fresh_name
from aeon.synthesis.modules.synquid.round_trip import ApplicationState, erase, match_result
from aeon.synthesis.modules.synquid.solver import SearchStats, Status
from aeon.synthesis.modules.synquid.abduction import abduce, branch_environment
from aeon.synthesis.modules.synquid.guards import (
    bool_pairwise_conjunctions,
    bool_quad_conjunctions,
    bool_terms_from_qualifier_atoms,
    bool_triple_conjunctions,
)
from aeon.typechecking.context import TypingContext
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.utils.name import Name


def monomorfic(t: Type, typing_ctx: TypingContext, t_l: dict[Name, Type]):
    match t:
        case TypePolymorphism(var_name, _, var_body):
            for t in [
                t
                for n, t in typing_ctx.concrete_vars()
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


def _solve_literal(ret_t: Type, base_t: TypeConstructor):
    """Propose one SMT model literal; final checking still proves the goal.

    Free context variables are existential in this proposal query. A chosen
    literal is not thereby proved valid for every value of those variables.
    """
    from z3 import Solver, sat

    from aeon.core.liquid import LiquidLiteralBool
    from aeon.verification.smt import make_variable, translate_liq

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
        s.set(timeout=100)
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
    """Prune a known invalid obligation, retaining unknown/unsupported results."""
    from aeon.typechecking.typeinfer import check

    trial = state.fork() if state is not None else ConstraintState(ctx)
    try:
        trial.add(check(trial.context, term, goal))
        return trial.solve() not in (Status.INVALID, Status.EXHAUSTED)
    except Exception:
        return True


def _arg_gen(ctx, level, goal, skip, mem, state):
    unknowns = state.unresolved(goal)
    if unknowns:
        # Shape discovery for type variables not anchored by the result. Each
        # candidate supplies its actual shape; refinements are inferred jointly
        # only after selection. Deeper candidates use the same finite shapes.
        shapes = [
            erase(t)
            for n, t in ctx.concrete_vars()
            if not skip(n) and isinstance(t, (TypeConstructor, RefinedType, TypeVar))
        ]
        shapes += [TypeConstructor(Name(n, 0)) for n in ("Int", "Bool", "String")]
        seen = set()
        for shape in shapes:
            if shape in seen or match_result(goal, shape, unknowns) is None:
                continue
            seen.add(shape)
            yield from synthes_memory(ctx, max(0, level - 1), shape, skip, mem, state)
        return
    depth = level - 1 if isinstance(erase(goal), (TypeConstructor, AbstractionType)) else 0
    yield from synthes_memory(ctx, max(0, depth), goal, skip, mem, state)


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
                # Retain unsupported fragments for whole-program checking.
                # Do not invent facts from an argument whose inference failed.
                child = ApplicationState(
                    application.state.fork(),
                    application.params[1:],
                    application.result,
                    application.goal,
                    application.deferred,
                )
                binder, _ = application.params[0]
                child.params = [(n, substitution_in_type(t, argument, binder)) for n, t in child.params]
                child.result = substitution_in_type(child.result, argument, binder)
                child.deferred = [(n, substitution_in_type(t, argument, binder)) for n, t in child.deferred]
            new_head = substitution(head, argument, binder) if filling else Application(head, argument)
            yield from _application_terms(ctx, level, new_head, child, skip, mem, filling)


def _materialize_term(term, assignment, state):
    if isinstance(term, TypeApplication):
        return TypeApplication(
            _materialize_term(term.body, assignment, state), state.materialize(term.type, assignment)
        )
    if isinstance(term, RefinementApplication):
        return RefinementApplication(_materialize_term(term.body, assignment, state), term.refinement)
    if isinstance(term, Application):
        return Application(
            _materialize_term(term.fun, assignment, state), _materialize_term(term.arg, assignment, state)
        )
    if isinstance(term, Annotation):
        return Annotation(_materialize_term(term.expr, assignment, state), state.materialize(term.type, assignment))
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
    # A context/level/type key cannot distinguish liquid assignments or pending
    # result obligations. Disable term memoization until state equivalence is
    # established; mem carries per-search instrumentation and the deadline only.
    if state is None:
        state = ConstraintState(
            ctx,
            stats=mem.setdefault("synquid_stats", SearchStats()),
            deadline=mem.get("synquid_deadline", float("inf")),
        )
    if monotonic() >= mem.get("synquid_deadline", float("inf")):
        return
    try:
        for item in synthes(ctx, level, ret_t, skip, mem, state, conditionals=conditionals):
            if monotonic() >= mem.get("synquid_deadline", float("inf")):
                return
            yield item
    except NotImplementedError:
        return


def match_type(t1: Type, t2: Type):
    if t1 == t2:
        return True
    elif type(t1) is type(t2):
        return False
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        return match_type(t1.var_type, t2.var_type) and match_type(t1.type, t2.type)
    else:
        return False


def synthes(
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
    base_t = erase(ret_t)
    if level == 0:
        arrow_goal: AbstractionType | None = ret_t if isinstance(ret_t, AbstractionType) else None
        if arrow_goal is None and isinstance(ret_t, RefinedType) and isinstance(ret_t.type, AbstractionType):
            arrow_goal = ret_t.type
        if arrow_goal is not None:
            for name, _ in [
                (n, t)
                for n, t in ctx.concrete_vars()
                if isinstance(t, AbstractionType) and match_result(t, arrow_goal, set()) is not None and not skip(n)
            ]:
                yield Var(name)
            return
        if isinstance(base_t, TypeVar):
            for name, t in ctx.concrete_vars():
                if t == base_t:
                    yield Var(name)
            return
        assert isinstance(base_t, TypeConstructor)
        for name, _ in [
            (n, t)
            for n, t in ctx.concrete_vars()
            if isinstance(t, (TypeConstructor, RefinedType)) and erase(t) == base_t and not skip(n)
        ]:
            if _local_check(ctx, Var(name), ret_t, state):
                yield Var(name)
        match base_t:
            case TypeConstructor(Name("Bool", 0)):
                yield from [Literal(True, base_t), Literal(False, base_t)]
            case TypeConstructor(Name("Int", 0)):
                # ?intLit: solved by z3 against the VC (goal refinement) here.
                yield from _solve_literal(ret_t, base_t)
            case TypeConstructor(Name("Float", 0)):
                # ?floatLit: solved by z3 against the VC (goal refinement) here.
                yield from _solve_literal(ret_t, base_t)
            case TypeConstructor(Name("String", 0)):
                yield from (
                    Literal(s, base_t)
                    for s in ("", " ", "a", "b", "0", "1", "x", "y", "\n", "\t", "true", "false", "[]", "{}", "nil")
                )
            case TypeConstructor(Name("Unit", 0)):
                yield Literal(None, base_t)
            case _:
                raise NotImplementedError
    elif level >= 1:
        arrow_syn: AbstractionType | None = ret_t if isinstance(ret_t, AbstractionType) else None
        if arrow_syn is None and isinstance(ret_t, RefinedType) and isinstance(ret_t.type, AbstractionType):
            arrow_syn = ret_t.type
        if arrow_syn is not None:
            ctx_l = ctx.with_var(arrow_syn.var_name, arrow_syn.var_type)
            for bod in synthes_memory(
                ctx_l,
                level - 1,
                arrow_syn.type,
                skip,
                mem,
                state.fork(state.context.with_var(arrow_syn.var_name, arrow_syn.var_type)),
            ):
                lam = Abstraction(arrow_syn.var_name, bod)
                if isinstance(ret_t, RefinedType):
                    yield Annotation(lam, ret_t)
                else:
                    yield lam
        for name, typ in [
            (n, ty)
            for n, ty in ctx.concrete_vars()
            if not isinstance(ty, (TypeConstructor, RefinedType)) and not skip(n)
        ]:
            if monotonic() >= mem.get("synquid_deadline", float("inf")):
                return
            branch_state = state.fork()
            tyvars, inner = _peel_polymorphism(typ)
            _, result = _uncurry_arrow_b(inner)
            shape = match_result(result, ret_t, set(tyvars))
            if shape is None:
                continue
            head: Term = Var(name)
            atoms = extract_qualifier_atoms(ctx, goal_type=ret_t)
            inner = typ
            while isinstance(inner, (TypePolymorphism, RefinementPolymorphism)):
                if isinstance(inner, TypePolymorphism):
                    tv = inner.name
                    if tv in shape:
                        instance = branch_state.fresh_type(shape[tv], atoms)
                    else:
                        instance = TypeVar(fresh_name("type"))
                        branch_state.type_unknowns |= {instance.name}
                    inner = type_substitution(inner.body, tv, instance)
                    head = TypeApplication(head, instance)
                else:
                    predicate = branch_state.refinement_parameter(inner.sort)
                    inner = instantiate_refinement_with_horn_in_type(inner.body, inner.name, inner.sort, predicate.name)
                    head = RefinementApplication(head, ImplicitRefinementHole(fresh_name("implicit")))
            application = ApplicationState.start(branch_state, inner, ret_t)
            yield from _application_terms(ctx, level, head, application, skip, mem)
        if not conditionals:
            return
        # IFAB proposes an E-term, solves for κ, realizes its Boolean expression,
        # and recursively constructs the else branch with ¬κ in the environment.
        fallback = False
        proposals = synthes_memory(
            ctx, level - 1, ret_t, skip, mem, branch_environment(state, ret_t), conditionals=False
        )
        for then in islice(proposals, 64):
            if monotonic() >= mem.get("synquid_deadline", float("inf")):
                return
            abduction = abduce(state, then, ret_t)
            fallback |= abduction.status in (Status.UNKNOWN, Status.UNSUPPORTED, Status.EXHAUSTED)
            for condition, guard in abduction.guards:
                if condition == LiquidLiteralBool(True):
                    if _local_check(ctx, then, ret_t, state):
                        yield then
                    continue
                state.stats.abduced_guards += 1
                otherwise_state = state.assume(negate(condition))
                for otherwise in synthes_memory(ctx, level - 1, ret_t, skip, mem, otherwise_state):
                    if _local_check(ctx, otherwise, ret_t, otherwise_state):
                        yield Annotation(If(guard, then, otherwise), ret_t)
        # Bounded qualifier enumeration remains a fallback outside IFAB's
        # supported/available vocabulary. Both branches still see their path.
        if fallback:
            atoms = extract_qualifier_atoms(ctx, goal_type=ret_t)
            guards = chain(
                bool_terms_from_qualifier_atoms(ctx, atoms),
                bool_pairwise_conjunctions(ctx, atoms),
                bool_triple_conjunctions(ctx, atoms),
                bool_quad_conjunctions(ctx, atoms),
            )
            from aeon.core.substitutions import liquefy

            for guard in guards:
                guard = guard.expr if isinstance(guard, Annotation) else guard
                condition = liquefy(guard)
                if condition is None:
                    continue
                state.stats.fallback_guards += 1
                then_state, else_state = state.assume(condition), state.assume(negate(condition))
                if then_state.inhabited() == Status.VALID or else_state.inhabited() == Status.VALID:
                    continue
                for then in synthes_memory(ctx, level - 1, ret_t, skip, mem, then_state):
                    if not _local_check(ctx, then, ret_t, then_state):
                        continue
                    for otherwise in synthes_memory(ctx, level - 1, ret_t, skip, mem, else_state):
                        if _local_check(ctx, otherwise, ret_t, else_state):
                            yield Annotation(If(guard, then, otherwise), ret_t)
