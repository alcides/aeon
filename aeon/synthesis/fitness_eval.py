"""Shared fitness evaluation helpers: prefix pre-binding, goal bundling, memoization."""

from __future__ import annotations

import dataclasses
from collections import OrderedDict
from collections.abc import Callable
from typing import Any

from aeon.backend.evaluator import EvaluationContext, eval as aeon_eval
from aeon.core.terms import Application, Let, Rec, Term, Var
from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.decorators import Goal
from aeon.synthesis.resource_meters import measure_cputime, measure_energy
from aeon.utils.name import Name

Computation = Callable[[Term], Any]

# Bound duplicate-phenotype memoization during a synthesis run.
_FITNESS_MEMO_MAX = 4096


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


def _eval_goal(
    suffix: Term,
    prefix_ctx: EvaluationContext,
    goal: Goal,
) -> float:
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
) -> dict[Name, float]:
    """Walk the suffix chain once, collecting expression goal values."""
    values: dict[Name, float] = {}
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
    own evaluation paths.

    The static prefix before ``fun_name`` is evaluated once from
    ``prefix_prog``; each candidate only extracts its suffix (no re-eval of
    library bindings).
    """
    prefix_ctx, _ = prebind_prefix(prefix_prog, ectx, fun_name)
    expr_functions = {g.function for g in goals if g.kind == "expression"}

    def fitness(prog: Term) -> list[float]:
        properties = iter(property_evaluators or [])
        suffix = extract_suffix(prog, fun_name)
        expr_values = _collect_expression_goals(suffix, prefix_ctx, expr_functions) if expr_functions else {}
        scores: list[float] = []
        for goal in goals:
            if goal.kind == "property":
                prop = next(properties)
                scores.append(prop(prog))
            elif goal.kind == "expression":
                if goal.function in expr_values:
                    scores.append(expr_values[goal.function])
                else:
                    scores.append(_eval_goal(suffix, prefix_ctx, goal))
            else:
                scores.append(_eval_goal(suffix, prefix_ctx, goal))
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
