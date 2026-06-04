"""Discover, generate inputs for, check, and report ``@property`` tests.

The runner reuses already-parsed artifacts from :class:`AeonDriver` (the typing
context, the core program, the evaluation context and the metadata). For each
property it derives a random-input generator from each argument's type
(:mod:`aeon.synthesis.pbt.generators`), evaluates the property on the sampled
inputs by replacing the program's tail expression with the call (so all
top-level definitions stay in scope), and reports the first counterexample.
"""

from __future__ import annotations

import signal
import threading
from dataclasses import dataclass, replace as dc_replace

from aeon.backend.evaluator import EvaluationContext, eval as aeon_eval
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Annotation, Application, Let, Rec, Term, Var
from aeon.core.types import AbstractionType, RefinementPolymorphism, Type, TypePolymorphism, t_bool
from aeon.decorators.api import Metadata
from aeon.sugar.lifting import lift
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm

DEFAULT_SAMPLES = 100
# Per-trial wall-clock guard (seconds): generated inputs can, in principle,
# drive recursive functions in scope into long/non-terminating evaluation.
DEFAULT_TIMEOUT = 5.0


@dataclass
class PropertyResult:
    """Outcome of checking a single property."""

    name: Name
    passed: bool
    trials: int
    counterexample: list[str] | None = None  # pretty-printed argument terms
    error: str | None = None  # message when the property could not be checked / crashed

    def summary(self) -> str:
        if self.error is not None and self.passed:
            return f"SKIP {self.name.name}: {self.error}"
        if self.passed:
            return f"PASS {self.name.name} ({self.trials} samples)"
        head = f"FAIL {self.name.name} (after {self.trials} samples)"
        if self.counterexample is not None:
            args = ", ".join(self.counterexample) if self.counterexample else "<no arguments>"
            head += f"\n     counterexample: {args}"
        if self.error is not None:
            head += f"\n     raised: {self.error}"
        return head


class _Timeout(Exception):
    pass


def _replace_tail(program: Term, new_tail: Term) -> Term:
    """Replace a program's tail expression (the ``main`` slot) with ``new_tail``,
    keeping every top-level binding in scope.

    Walks the ``Rec``/``Let``/``Annotation`` chain of top-level definitions to
    its innermost body and swaps it out. This is robust regardless of whether the
    tail is a synthesised ``main`` hole or a user-defined ``main`` application —
    unlike substituting a fixed ``Name("main", 0)``, which only matches the hole."""
    match program:
        case Rec():
            return dc_replace(program, body=_replace_tail(program.body, new_tail))
        case Let():
            return dc_replace(program, body=_replace_tail(program.body, new_tail))
        case Annotation():
            return dc_replace(program, expr=_replace_tail(program.expr, new_tail))
        case _:
            return new_tail


def _decompose(ty: Type) -> tuple[list[tuple[Name, Type]], Type]:
    """Split a (possibly curried) function type into its argument specs and the
    return type. Argument refinements are preserved (they act as preconditions)."""
    args: list[tuple[Name, Type]] = []
    while isinstance(ty, AbstractionType):
        args.append((ty.var_name, ty.var_type))
        ty = ty.type
    return args, ty


def _render(term: Term) -> str:
    """Best-effort surface-syntax rendering of an argument term for reporting."""
    try:
        return pretty_print_sterm(lift(term))
    except Exception:
        return repr(term)


def _eval_bool(program: Term, ectx: EvaluationContext, timeout: float) -> tuple[bool | None, str | None]:
    """Evaluate ``program`` to a Python ``bool``.

    Returns ``(value, None)`` on success, ``(None, message)`` when evaluation
    raised or timed out. A SIGALRM guard bounds runaway evaluation; it is only
    armed on the main thread of a platform that supports it (so it stays inert
    under pytest worker threads / Windows), otherwise evaluation runs unguarded.
    """
    can_alarm = hasattr(signal, "SIGALRM") and threading.current_thread() is threading.main_thread()

    def _handler(signum, frame):
        raise _Timeout()

    old_handler = None
    if can_alarm:
        old_handler = signal.signal(signal.SIGALRM, _handler)
        signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        result = aeon_eval(program, ectx)
    except _Timeout:
        return None, f"timeout after {timeout:g}s"
    except Exception as e:  # a crashing input is itself a useful counterexample
        return None, f"{type(e).__name__}: {e}"
    finally:
        if can_alarm:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old_handler)
    if not isinstance(result, bool):
        return None, f"property did not evaluate to a Bool (got {type(result).__name__})"
    return result, None


@dataclass
class _PropertySpec:
    name: Name
    arg_specs: list[tuple[Name, Type]]
    samples: int


def _iter_top_level(core: Term):
    """Yield ``(name, type)`` for each top-level definition (``Rec`` binding) by
    walking the program's binding chain to the tail. Top-level user definitions
    live here — not in the typing context, which holds only the prelude."""
    t = core
    while True:
        match t:
            case Rec():
                yield t.var_name, t.var_type
                t = t.body
            case Let():
                t = t.body
            case Annotation():
                t = t.expr
            case _:
                return


def _collect_properties(core: Term, metadata: Metadata) -> tuple[list[_PropertySpec], list[PropertyResult]]:
    """Find ``@property`` functions among the program's top-level definitions and
    decompose their types. Returns runnable specs plus skip results for
    malformed properties (polymorphic, or not returning ``Bool``).

    Property names are matched by string; ``metadata`` is keyed by the surface
    ``Definition.name`` whose id normally matches the resolved core name, but a
    string match is robust even if it does not (see ``bind_ids``)."""
    config_by_name: dict[str, dict] = {}
    for key, entry in metadata.items():
        if isinstance(key, Name) and isinstance(entry, dict) and "property" in entry:
            config_by_name[key.name] = entry["property"] or {}

    specs: list[_PropertySpec] = []
    skips: list[PropertyResult] = []
    seen: set[str] = set()
    for name, ty in _iter_top_level(core):
        if name.name not in config_by_name or name.name in seen:
            continue
        seen.add(name.name)
        if isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            skips.append(
                PropertyResult(name, passed=True, trials=0, error="polymorphic properties are not yet supported")
            )
            continue
        arg_specs, ret = _decompose(ty)
        if ret != t_bool:
            skips.append(PropertyResult(name, passed=True, trials=0, error=f"return type must be Bool, got {ret}"))
            continue
        samples = config_by_name[name.name].get("samples") or DEFAULT_SAMPLES
        specs.append(_PropertySpec(name, arg_specs, samples))
    return specs, skips


def _check_property(
    spec: _PropertySpec,
    typing_ctx: TypingContext,
    evaluation_ctx: EvaluationContext,
    core: Term,
    metadata: Metadata,
    seed: int,
    timeout: float,
) -> PropertyResult:
    from aeon.synthesis.pbt.generators import TypeSampler

    # Cache one sampler per distinct argument type. A non-dependent argument has
    # the same type every trial, so its (expensive) grammar is built once and the
    # sampler's RNG advances across draws. A dependent argument's type differs per
    # trial (an earlier choice is substituted in), yielding a fresh key each time.
    sampler_cache: dict[str, TypeSampler] = {}

    def sampler_for(ty: Type, idx: int) -> TypeSampler:
        key = f"{idx}:{ty!r}"
        sampler = sampler_cache.get(key)
        if sampler is None:
            sampler = TypeSampler(typing_ctx, ty, spec.name, metadata, seed=seed + idx * 7919)
            sampler_cache[key] = sampler
        return sampler

    for trial in range(spec.samples):
        chosen: list[tuple[Name, Term]] = []
        terms: list[Term] = []
        # Generate arguments left-to-right so a later argument's refinement that
        # mentions an earlier argument is specialised to the concrete choice.
        for idx, (arg_name, arg_type) in enumerate(spec.arg_specs):
            ty = arg_type
            for prev_name, prev_term in chosen:
                ty = substitution_in_type(ty, prev_term, prev_name)
            term = sampler_for(ty, idx).sample()
            chosen.append((arg_name, term))
            terms.append(term)

        call: Term = Var(spec.name)
        for term in terms:
            call = Application(call, term)
        program = _replace_tail(core, call)

        value, error = _eval_bool(program, evaluation_ctx, timeout)
        if value is not True:
            return PropertyResult(
                name=spec.name,
                passed=False,
                trials=trial + 1,
                counterexample=[_render(t) for t in terms],
                error=error,
            )
    return PropertyResult(spec.name, passed=True, trials=spec.samples)


def run_properties(
    typing_ctx: TypingContext,
    evaluation_ctx: EvaluationContext,
    core: Term,
    metadata: Metadata,
    seed: int = 0,
    timeout: float = DEFAULT_TIMEOUT,
) -> list[PropertyResult]:
    """Check every ``@property`` function and return one result per property."""
    specs, skips = _collect_properties(core, metadata)
    results: list[PropertyResult] = list(skips)
    for spec in specs:
        results.append(_check_property(spec, typing_ctx, evaluation_ctx, core, metadata, seed=seed, timeout=timeout))
    return results
