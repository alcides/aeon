"""Shared fitness evaluation helpers: prefix pre-binding, goal bundling, memoization."""

from __future__ import annotations

import dataclasses
from collections import OrderedDict
from collections.abc import Callable
from typing import Any

from aeon.backend.evaluator import EvaluationContext, eval as aeon_eval
from aeon.core.terms import Application, Hole, Let, Literal, Rec, Term, Var
from aeon.core.types import t_int
from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.decorators import Goal
from aeon.synthesis.identification import term_has_holes
from aeon.synthesis.resource_meters import measure_cputime, measure_energy
from aeon.utils.name import Name

Computation = Callable[[Term], Any]

# Bound duplicate-phenotype memoization during a synthesis run.
_FITNESS_MEMO_MAX = 4096


def require_complete_program(prog: Term) -> None:
    """Fitness must never execute an unresolved candidate or placeholder bundle."""
    if term_has_holes(without_main_placeholder(prog)):
        raise InvalidIndividualException()


def without_main_placeholder(prog: Term) -> Term:
    """Remove only the compiler's synthetic, unused entrypoint placeholder.

    It is not a synthesis target and fitness replaces the program tail with
    an objective. Named user holes (including a bound ?main) still count.
    """
    tail = prog
    while isinstance(tail, (Let, Rec)):
        tail = tail.body
    if isinstance(tail, Hole) and tail.name == Name("main", 0):
        return set_program_tail(prog, Literal(1, t_int))
    return prog


def set_program_tail(term: Term, new_tail: Term) -> Term:
    """Replace the innermost body of a chain of top-level ``let``/``rec``
    bindings with ``new_tail`` (the bindings, and so everything in scope, stay)."""
    if isinstance(term, (Let, Rec)):
        return dataclasses.replace(term, body=set_program_tail(term.body, new_tail))
    return new_tail


def candidate_key(term: Term) -> int:
    """Stable structural hash for memo keys (ignores source locations)."""
    return hash(term)


def extract_suffix(prog: Term, stop_before: Name) -> Term:
    """Return the ``let``/``rec`` chain starting at ``stop_before`` without evaluating.

    Used when the program prefix before the synthesised binding is known to be
    identical to a previously pre-bound program (only the hole body changes).
    """
    t = prog
    while isinstance(t, (Let, Rec)):
        if t.var_name == stop_before:
            return t
        t = t.body
    return prog


def prebind_prefix(
    prog: Term,
    ectx: EvaluationContext,
    stop_before: Name,
) -> tuple[EvaluationContext, Term]:
    """Evaluate static ``let``/``rec`` bindings before ``stop_before``.

    Returns the extended context and the suffix starting at the ``stop_before``
    binding (or the original program when that name is not found).
    """
    ctx = ectx
    t = prog
    while isinstance(t, (Let, Rec)):
        if t.var_name == stop_before:
            return ctx, t
        bound = aeon_eval(dataclasses.replace(t, body=Var(t.var_name)), ctx)
        ctx = ctx.with_var(t.var_name, bound)
        t = t.body
    return ctx, t


def as_objective_vector(value: Any, length: int) -> list[float]:
    """Normalize a fitness helper return value to ``length`` floats.

    Single-objective goals yield a scalar. Multi-objective goals
    (``@multi_minimize_*`` / ``@multi_maximize_*``) evaluate to a native
    ``Array``, which is a Python ``list`` at runtime (see issue #294).
    """
    if length < 1:
        raise InvalidIndividualException()
    if length == 1:
        if isinstance(value, (list, tuple)):
            if len(value) != 1:
                raise InvalidIndividualException()
            value = value[0]
        try:
            return [float(value)]
        except (TypeError, ValueError):
            raise InvalidIndividualException()
    if not isinstance(value, (list, tuple)) or len(value) != length:
        raise InvalidIndividualException()
    try:
        return [float(x) for x in value]
    except (TypeError, ValueError):
        raise InvalidIndividualException()


def _eval_goal(
    suffix: Term,
    prefix_ctx: EvaluationContext,
    goal: Goal,
) -> Any:
    """Evaluate one generated-helper goal against an already-extracted suffix."""
    program_for_fitness = set_program_tail(suffix, Var(goal.function))
    try:
        if goal.kind == "cputime":
            return measure_cputime(lambda: aeon_eval(program_for_fitness, prefix_ctx))
        if goal.kind == "energy":
            return measure_energy(lambda: aeon_eval(program_for_fitness, prefix_ctx))
        return aeon_eval(program_for_fitness, prefix_ctx)
    except Exception:
        raise InvalidIndividualException()


def _collect_expression_goals(
    suffix: Term,
    prefix_ctx: EvaluationContext,
    expr_functions: set[Name],
) -> dict[Name, Any]:
    """Walk the suffix chain once, collecting expression goal values."""
    values: dict[Name, Any] = {}
    ctx = prefix_ctx
    t = suffix
    while isinstance(t, (Let, Rec)):
        try:
            bound = aeon_eval(dataclasses.replace(t, body=Var(t.var_name)), ctx)
        except Exception:
            raise InvalidIndividualException()
        ctx = ctx.with_var(t.var_name, bound)
        if t.var_name in expr_functions:
            values[t.var_name] = bound
        t = t.body
    return values


def make_bundled_fitness_evaluator(
    goals: list[Goal],
    ectx: EvaluationContext,
    fun_name: Name,
    prefix_prog: Term,
    property_evaluators: list[Callable[[Term], float]] | None = None,
) -> Callable[[Term], list[float]]:
    """Return one evaluator that scores every goal for a substituted program.

    Expression goals on the suffix ``rec`` chain share a single interpreter
    walk; ``cputime``/``energy`` and ``property`` goals fall back to their
    own evaluation paths. Multi-objective expression goals expand their
    native ``Array`` return into ``goal.length`` floats so the vector lines
    up with ``minimize_flags_from_goals``.

    The static prefix before ``fun_name`` is evaluated once from
    ``prefix_prog``; each candidate only extracts its suffix (no re-eval of
    library bindings).
    """
    # A legacy per-hole caller may still have open siblings in its prefix.
    # Defer that prefix rather than evaluating holes during fitness setup.
    current = prefix_prog
    dynamic_prefix = False
    while isinstance(current, (Let, Rec)) and current.var_name != fun_name:
        if term_has_holes(current.var_value):
            dynamic_prefix = True
            break
        current = current.body
    prefix_ctx = None if dynamic_prefix else prebind_prefix(prefix_prog, ectx, fun_name)[0]
    expr_functions = {g.function for g in goals if g.kind == "expression"}

    def fitness(prog: Term) -> list[float]:
        require_complete_program(prog)
        properties = iter(property_evaluators or [])
        if prefix_ctx is None:
            candidate_ctx, suffix = prebind_prefix(prog, ectx, fun_name)
        else:
            candidate_ctx, suffix = prefix_ctx, extract_suffix(prog, fun_name)
        expr_values = _collect_expression_goals(suffix, candidate_ctx, expr_functions) if expr_functions else {}
        scores: list[float] = []
        for goal in goals:
            if goal.kind == "property":
                prop = next(properties)
                scores.extend(as_objective_vector(prop(prog), goal.length))
            elif goal.kind == "expression":
                if goal.function in expr_values:
                    raw = expr_values[goal.function]
                else:
                    raw = _eval_goal(suffix, candidate_ctx, goal)
                scores.extend(as_objective_vector(raw, goal.length))
            else:
                scores.extend(as_objective_vector(_eval_goal(suffix, candidate_ctx, goal), goal.length))
        return scores

    return fitness


def memoize_fitness(comp: Computation, maxsize: int = _FITNESS_MEMO_MAX) -> Computation:
    """LRU memo keyed by ``candidate_key`` for duplicate phenotypes."""
    cache: OrderedDict[int, Any] = OrderedDict()

    def wrapped(prog: Term) -> Any:
        key = candidate_key(prog)
        hit = cache.get(key)
        if hit is not None:
            cache.move_to_end(key)
            return hit
        result = comp(prog)
        cache[key] = result
        if len(cache) > maxsize:
            cache.popitem(last=False)
        return result

    return wrapped


def prebuild_property_calls(spec_name: Name, cases: tuple[tuple[Term, ...], ...]) -> tuple[Term, ...]:
    """Build property application spines once for a fixed corpus."""
    calls: list[Term] = []
    for args in cases:
        call: Term = Var(spec_name)
        for arg in args:
            call = Application(call, arg)
        calls.append(call)
    return tuple(calls)
