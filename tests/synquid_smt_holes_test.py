"""Tests for synquid's two-step shape-then-fill SMT placeholder pipeline."""

from __future__ import annotations

from aeon.core.terms import (
    Annotation,
    Application,
    Hole,
    If,
    Literal,
    Var,
)
from aeon.core.types import (
    TypeConstructor,
    t_bool,
    t_float,
    t_int,
)
from aeon.synthesis.modules.synquid.smt_holes import (
    collect_placeholders,
    fill_placeholders,
    smt_complete,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _placeholder(prefix: str, idx: int, ty) -> Annotation:
    return Annotation(Hole(Name(prefix, idx)), ty)


def test_collect_placeholders_finds_nested_holes():
    a = _placeholder("h", 1, t_int)
    b = _placeholder("h", 2, t_float)
    term = If(
        Annotation(Application(Var(Name("<", 0)), a), t_bool),
        b,
        Var(Name("x", 0)),
    )
    found = collect_placeholders(term)
    names = [n for (n, _) in found]
    assert Name("h", 1) in names
    assert Name("h", 2) in names
    assert len(found) == 2


def test_collect_placeholders_ignores_concrete_terms():
    term = If(
        Application(Var(Name("<", 0)), Literal(1, t_int)),
        Literal(0, t_int),
        Literal(1, t_int),
    )
    assert collect_placeholders(term) == []


def test_fill_placeholders_replaces_by_name():
    h1 = Name("h", 1)
    h2 = Name("h", 2)
    term = Application(_placeholder("h", 1, t_int), _placeholder("h", 2, t_int))
    filled = fill_placeholders(
        term,
        {h1: Literal(7, t_int), h2: Literal(42, t_int)},
    )
    assert filled == Application(Literal(7, t_int), Literal(42, t_int))


def test_smt_complete_falls_back_to_seed_when_unconstrained():
    """No refinement constraints in scope, so z3 returns nothing — the
    seed table fills in canonical values."""
    ctx = TypingContext()
    term = _placeholder("h", 99, t_float)
    completed = smt_complete(term, ctx, seed_idx=0)
    assert completed == Literal(0.0, t_float)


def test_smt_complete_seed_idx_cycles_values():
    ctx = TypingContext()
    term = _placeholder("h", 99, t_int)
    seen = {smt_complete(term, ctx, seed_idx=i).value for i in range(5)}
    # The Int seed table is [0, 1, -1, 2, 10] — five distinct values.
    assert seen == {0, 1, -1, 2, 10}


def test_smt_complete_passthrough_when_no_placeholders():
    ctx = TypingContext()
    term = If(Literal(True, t_bool), Literal(1, t_int), Literal(2, t_int))
    assert smt_complete(term, ctx) is term


def test_smt_complete_returns_none_for_unsupported_type():
    """A placeholder annotated with a type the seed table doesn't know
    about (here: a synthetic Wibble type) returns None so the caller
    skips the candidate."""
    ctx = TypingContext()
    wibble = TypeConstructor(Name("Wibble", 0))
    term = Annotation(Hole(Name("h", 99)), wibble)
    assert smt_complete(term, ctx) is None
