"""Helpers for materializing aeon `Term` objects from LTA transitions.

Each transition's symbol determines how to assemble a `Term` from the terms
denoted by its incoming states. Only expression-level kinds produce a
non-`None` result; type-level kinds (KIND_BASE_REF, KIND_ARROW_TYPE, ...) live
in the type sub-automaton and do not directly yield terms.
"""

from __future__ import annotations

from typing import Sequence

from aeon.core.terms import Application, If, Literal, Term, Var
from aeon.core.types import Type
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

from aeon.synthesis.modules.lta.automaton import (
    KIND_APP,
    KIND_CONST,
    KIND_GOAL,
    KIND_IF,
    KIND_TYPE_APP,
    KIND_VAR,
    Transition,
)


_loc = SynthesizedLocation("lta")


def term_for_transition(t: Transition, children: Sequence[Term]) -> Term | None:
    """Produce the aeon `Term` denoted by `t` given terms for its incoming
    state denotations, or `None` for type-level/abstract transitions.

    For expression-level kinds, the *first* incoming state is conventionally
    the transition's type sub-automaton (see Fig. 4 of the paper). Children
    corresponding to the type sub-automaton do not have term denotations and
    are passed through as `None` from the caller — we simply ignore them.
    """
    sym = t.symbol
    if sym.kind == KIND_VAR:
        # payload = Name
        name = sym.payload
        assert isinstance(name, Name)
        return Var(name, _loc)
    if sym.kind == KIND_CONST:
        # payload = (value, Type)
        payload = sym.payload
        assert isinstance(payload, tuple) and len(payload) == 2
        value, ty = payload
        assert isinstance(ty, Type)
        return Literal(value, ty, _loc)
    if sym.kind == KIND_TYPE_APP:
        # payload = the pre-built TypeApplication/RefinementApplication spine.
        head = sym.payload
        assert isinstance(head, Term)
        return head
    if sym.kind == KIND_APP:
        # Incoming layout: (type, function, argument). Type child has no term.
        # children come from denotation: for state q with aeon_type=None we
        # would have skipped — see automaton.denot_state. In practice the type
        # sub-automaton produces no terms, so children may be (fun, arg).
        if len(children) >= 2:
            fun, arg = children[-2], children[-1]
            return Application(fun, arg, _loc)
        return None
    if sym.kind == KIND_IF:
        if len(children) >= 3:
            cond, t_br, f_br = children[-3], children[-2], children[-1]
            return If(cond, t_br, f_br, _loc)
        return None
    if sym.kind == KIND_GOAL:
        # Goal is final: just forward the result expression (last incoming).
        return children[-1] if children else None
    # Type-level transitions don't produce terms.
    return None
