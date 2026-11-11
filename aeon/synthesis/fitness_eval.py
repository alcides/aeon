"""Shared fitness evaluation helpers: prefix pre-binding, goal bundling, memoization."""

from __future__ import annotations

import dataclasses
from collections import OrderedDict
from collections.abc import Callable
from math import isfinite
from typing import Any

from aeon.backend.evaluator import EvaluationContext, eval as aeon_eval
from aeon.core.terms import Application, Hole, Let, Literal, Rec, Term, Var
from aeon.core.types import t_int
from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.decorators import Goal
from aeon.synthesis.expression_size import make_size_evaluator
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


def candidate_key(term: Term) -> Term:
    """Structural key: dictionary lookup must check equality after hashing.

    Different literals (notably -1 and -2) can have identical Python hashes.
    Core terms already provide structural equality ignoring source locations.
    """
    return term


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
            scores = [float(value)]
        except (TypeError, ValueError, OverflowError):
            raise InvalidIndividualException()
    else:
        if not isinstance(value, (list, tuple)) or len(value) != length:
            raise InvalidIndividualException()
        try:
            scores = [float(x) for x in value]
        except (TypeError, ValueError, OverflowError):
            raise InvalidIndividualException()
    if not all(isfinite(score) for score in scores):
        raise InvalidIndividualException()
    return scores


def _require_slice(program: Term, function: Name) -> Term:
    """Evaluate only a requirement's dependencies, never unrelated objectives.

    Names are already uniquely bound. Keeping whole mutual groups preserves
    the interpreter's recursion environment when a requirement calls one.
    """
    bindings = []
    node = program
    while isinstance(node, (Let, Rec)):
        bindings.append(node)
        node = node.body
    by_name = {binding.var_name: binding for binding in bindings}

    def references(value):
        if isinstance(value, Var):
            yield value.name
        elif isinstance(value, Term) and dataclasses.is_dataclass(value):
            for field in dataclasses.fields(value):
                yield from references(getattr(value, field.name))
        elif isinstance(value, (tuple, list)):
            for item in value:
                yield from references(item)

    needed = set()
    pending = [function]
    while pending:
        name = pending.pop()
        if name in needed or name not in by_name:
            continue
        needed.add(name)
        binding = by_name[name]
        pending.extend(references(binding.var_value))
        group = getattr(binding, "mutual_group_id", None)
        if group is not None:
            pending.extend(b.var_name for b in bindings if getattr(b, "mutual_group_id", None) == group)
    result: Term = Var(function)
    for binding in reversed(bindings):
        if binding.var_name in needed:
            result = dataclasses.replace(binding, body=result)
    return result


class CandidateEvaluationCache:
    """One candidate's runtime bindings, shared by checks and objective scoring.

    Only the most recent program is retained. New candidates cannot inherit
    values or failures from the previous candidate.
    """

    def __init__(self):
        self.program: Term | None = None
        self.context: EvaluationContext | None = None
        self.values: dict[Name, Any] = {}
        self.failures: set[Name] = set()

    def evaluate(self, program: Term, suffix: Term, context: EvaluationContext, function: Name) -> Any:
        if self.program is None or self.program != program:
            self.program = program
            self.context = context
            self.values = {}
            self.failures = set()
        if function in self.failures:
            raise InvalidIndividualException()
        if function in self.values:
            return self.values[function]
        # Dependency slicing avoids executing unrelated objective helpers before
        # requirements pass. Bindings already computed by another check/goal
        # are reused from the same runtime environment.
        node = _require_slice(suffix, function)
        try:
            while isinstance(node, (Let, Rec)):
                group = getattr(node, "mutual_group_id", None)
                if group is not None:
                    members = []
                    while isinstance(node, Rec) and node.mutual_group_id == group:
                        members.append(node)
                        node = node.body
                    for member in members:
                        if member.var_name not in self.values:
                            group_term: Term = Var(member.var_name)
                            for binding in reversed(members):
                                group_term = dataclasses.replace(binding, body=group_term)
                            self.values[member.var_name] = aeon_eval(group_term, self.context)
                    for member in members:
                        self.context = self.context.with_var(member.var_name, self.values[member.var_name])
                    continue
                if node.var_name not in self.values:
                    self.values[node.var_name] = aeon_eval(
                        dataclasses.replace(node, body=Var(node.var_name)), self.context
                    )
                    self.context = self.context.with_var(node.var_name, self.values[node.var_name])
                node = node.body
            if function not in self.values:
                self.values[function] = aeon_eval(Var(function), self.context)
            return self.values[function]
        except Exception:
            self.failures.add(function)
            raise InvalidIndividualException()


def _eval_goal(
    suffix: Term,
    prefix_ctx: EvaluationContext,
    goal: Goal,
) -> Any:
    """Evaluate one generated-helper goal against an already-extracted suffix."""
    program_for_fitness = (
        _require_slice(suffix, goal.function)
        if goal.kind == "require"
        else set_program_tail(suffix, Var(goal.function))
    )
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
    runtime_cache: CandidateEvaluationCache | None = None,
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

    For size objectives, ``prefix_prog`` must retain the original holes so
    only their replacements are measured. Size-only scoring never evaluates
    program bindings.
    """
    if runtime_cache is None and any(g.kind == "require" for g in goals):
        runtime_cache = CandidateEvaluationCache()
    size_evaluators = {g.function: make_size_evaluator(prefix_prog, g.function) for g in goals if g.kind == "size"}
    needs_runtime = any(g.kind not in {"size", "property"} for g in goals)
    # A legacy per-hole caller may still have open siblings in its prefix.
    # Defer that prefix rather than evaluating holes during fitness setup.
    current = prefix_prog
    dynamic_prefix = False
    while isinstance(current, (Let, Rec)) and current.var_name != fun_name:
        if term_has_holes(current.var_value):
            dynamic_prefix = True
            break
        current = current.body
    prefix_ctx = (
        ectx if not needs_runtime else None if dynamic_prefix else prebind_prefix(prefix_prog, ectx, fun_name)[0]
    )
    expr_functions = {g.function for g in goals if g.kind in ("expression", "example", "csv", "constraint")}

    def fitness(prog: Term) -> list[float]:
        require_complete_program(prog)
        properties = iter(property_evaluators or [])
        if prefix_ctx is None:
            candidate_ctx, suffix = prebind_prefix(prog, ectx, fun_name)
        else:
            candidate_ctx, suffix = prefix_ctx, extract_suffix(prog, fun_name)
        # Mandatory checks run before any objective evaluation and contribute
        # no dimensions to the Pareto vector. Exceptions are candidate rejection.
        for goal in goals:
            if goal.kind == "require" and runtime_cache.evaluate(prog, suffix, candidate_ctx, goal.function) != 0:
                raise InvalidIndividualException("candidate violates @require")
        expr_values = (
            {
                goal.function: runtime_cache.evaluate(prog, suffix, candidate_ctx, goal.function)
                for goal in goals
                if goal.function in expr_functions
            }
            if runtime_cache is not None
            else _collect_expression_goals(suffix, candidate_ctx, expr_functions)
            if expr_functions
            else {}
        )
        scores: list[float] = []
        for goal in goals:
            if goal.kind == "require":
                continue
            if goal.kind == "size":
                scores.extend(size_evaluators[goal.function](prog))
            elif goal.kind == "property":
                prop = next(properties)
                scores.extend(as_objective_vector(prop(prog), goal.length))
            elif goal.kind in ("expression", "example", "csv", "constraint"):
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
    cache: OrderedDict[Term, Any] = OrderedDict()

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
