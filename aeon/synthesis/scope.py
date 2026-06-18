"""Hiding fitness-relevant helpers from the synthesis scope by let-shadowing.

The optimization decorators (``@minimize``, ``@example``, ``@cluster``, …) emit
auxiliary top-level definitions holding the fitness/example/cluster expressions.
They must stay in the program (so fitness evaluation can reach them), but must
not be offered to the synthesizers as building blocks.

This is the same problem the ``@hide`` decorator solved, and it is solved the
same way: lexical shadowing. ``TypingContext.concrete_vars()`` keeps the
innermost binding per surface name, so rebinding a helper to the inert ``Unit``
type at the synthesis point — exactly what ``let helper = unit in <hole>`` does —
hides its real (callable) type from the type-directed grammar and from every
backend. We gather the helper names from the ``Metadata`` that already records
them and append those ``Unit`` shadows to the context handed to synthesis.
"""

from __future__ import annotations

import dataclasses

from aeon.core.types import t_unit
from aeon.typechecking.context import (
    ReflectedBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.utils.name import Name

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


def shadow_fitness_helpers(ctx: TypingContext, metadata) -> TypingContext:
    """``ctx`` with every in-scope fitness/example/cluster helper let-shadowed to
    ``Unit``, so the synthesizer never builds it. Returns ``ctx`` unchanged when
    there is nothing to shadow. This mirrors a ``let helper = unit in <hole>``
    wrapper, relying on :meth:`TypingContext.concrete_vars` keeping the innermost
    (``Unit``) binding per name."""
    hidden = fitness_relevant_names(metadata)
    if not hidden:
        return ctx
    present = {e.name.name for e in ctx.entries if isinstance(e, _VALUE_BINDERS) and e.name.name in hidden}
    if not present:
        return ctx
    entries = list(ctx.entries)
    entries.extend(VariableBinder(Name(name, 0), t_unit) for name in sorted(present))
    return dataclasses.replace(ctx, entries=entries)
