"""Closing the synthesis scope over fitness-relevant definitions.

The optimization decorators (``@minimize``, ``@example``, ``@cluster``, …) emit
auxiliary top-level definitions holding the fitness/example/cluster expressions.
These must be evaluable (so they stay in the program, in scope for fitness
evaluation), but must *not* be visible to the synthesizers as building blocks —
otherwise the search would try to use a fitness function to build a candidate.

Rather than tagging those definitions with a magic ``__internal__`` name prefix
and filtering on it in every synthesizer, we gather their names from the
``Metadata`` that already records them and hand each synthesizer a *closed*
typing context with those bindings removed. The synthesis files own this
exclusion; the compiler is untouched.
"""

from __future__ import annotations

import dataclasses

from aeon.typechecking.context import (
    ReflectedBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)

_VALUE_BINDERS = (VariableBinder, UninterpretedBinder, ReflectedBinder)


def fitness_relevant_names(metadata) -> set[str]:
    """The (surface) names of every fitness/example/cluster helper recorded in
    ``metadata`` — the bindings that back ``@minimize``/``@maximize``,
    ``@example`` and ``@cluster`` and so must not appear in the synthesis scope."""
    names: set[str] = set()
    for entry in metadata.values():
        if not isinstance(entry, dict):
            continue
        for goal in entry.get("goals", []) or []:
            fn = getattr(goal, "function", None)
            if fn is not None:
                names.add(fn.name)
        for example in entry.get("examples", []) or []:
            fn = getattr(example, "function", None)
            if fn is not None:
                names.add(fn.name)
        cluster = entry.get("cluster")
        if cluster is not None:
            names.add(cluster.name)
    return names


def close_synthesis_context(ctx: TypingContext, metadata) -> TypingContext:
    """``ctx`` with the fitness-relevant value bindings removed — the closed
    scope a synthesizer should search in. Type-level binders are untouched, and
    the context is returned unchanged when there is nothing to hide."""
    hidden = fitness_relevant_names(metadata)
    if not hidden:
        return ctx
    kept = [e for e in ctx.entries if not (isinstance(e, _VALUE_BINDERS) and e.name.name in hidden)]
    if len(kept) == len(ctx.entries):
        return ctx
    return dataclasses.replace(ctx, entries=kept)
