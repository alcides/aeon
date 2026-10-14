"""Scope snapshots retain list semantics without copying every outer binder."""

import pytest
from hypothesis import given, strategies as st

from aeon.core.types import Kind, t_bool, t_int
from aeon.typechecking.context import TypeBinder, TypingContext, VariableBinder
from aeon.utils.name import Name


@given(st.integers(min_value=0, max_value=160), st.integers(min_value=-200, max_value=200))
def test_snapshot_indexing_and_slicing_match_lists(size, index):
    ctx = TypingContext()
    expected = list(ctx.entries)
    for i in range(size):
        ctx = ctx.with_var(Name("x", i), t_int)
        expected.append(VariableBinder(Name("x", i), t_int))
    assert list(ctx.entries) == expected
    assert list(reversed(ctx.entries)) == expected[::-1]
    assert ctx.entries[index:] == expected[index:]
    assert ctx.entries[::-2] == expected[::-2]
    if -len(expected) <= index < len(expected):
        assert ctx.entries[index] == expected[index]
    else:
        with pytest.raises(IndexError):
            ctx.entries[index]
    assert ctx.entries == expected
    assert expected == ctx.entries

    class Index:
        def __index__(self):
            return index

    if -len(expected) <= index < len(expected):
        assert ctx.entries[Index()] == expected[Index()]


def test_sibling_and_parent_mutations_are_isolated():
    parent = TypingContext().with_var(Name("outer"), t_int)
    original = list(parent.entries)
    left = parent.with_var(Name("left"), t_int)
    right = parent.with_typevar(Name("a"), Kind.BASE)
    parent.entries.clear()
    left.entries[0:2] = [VariableBinder(Name("replacement"), t_bool)]
    assert list(right.entries) == [*original, TypeBinder(Name("a"), Kind.BASE)]
    assert parent.entries == []
    # Extending a mutated snapshot freezes its current values, not the old ones.
    child = left.with_var(Name("child"), t_bool)
    frozen = list(child.entries)
    left.entries.reverse()
    left.entries.append(VariableBinder(Name("late"), t_int))
    assert list(child.entries) == frozen


def test_binder_mutations_remain_visible_in_derived_scopes():
    name = Name("outer")
    binder = VariableBinder(name, t_int)
    parent = TypingContext([binder]).with_var(Name("middle"), t_int)
    child = parent.with_var(Name("inner"), t_int)
    binder.type = t_bool
    assert child.type_of(name) == t_bool
    binder.name = Name("renamed")
    assert child.type_of(name) is None
    assert child.type_of(binder.name) == t_bool


def test_scope_extension_shares_complete_chunks():
    ctx = TypingContext()
    for i in range(256):
        ctx = ctx.with_var(Name("x", i), t_int)
    previous = ctx.entries
    child = ctx.with_var(Name("child"), t_int)
    # A deterministic complexity regression, rather than a flaky timing bound:
    # complete chunks are reused by identity, not copied entry-by-entry.
    assert child.entries._blocks is previous._blocks
    assert child.entries._tail[:-1] == previous._tail


@given(st.lists(st.tuples(st.integers(0, 5), st.integers(0, 20)), max_size=60))
def test_branching_scopes_match_independent_lists(operations):
    scopes = [TypingContext().with_var(Name("initial"), t_int)]
    expected = [list(scopes[0].entries)]
    for step, (operation, choice) in enumerate(operations):
        index = choice % len(scopes)
        ctx, reference = scopes[index], expected[index]
        binder = VariableBinder(Name("x", step), t_int)
        if operation == 0:
            scopes.append(ctx.with_var(binder.name, binder.type))
            expected.append([*reference, binder])
        elif operation == 1:
            ctx.entries.append(binder)
            reference.append(binder)
        elif operation == 2:
            ctx.entries[:] = [binder]
            reference[:] = [binder]
        elif operation == 3:
            ctx.entries.reverse()
            reference.reverse()
        elif operation == 4 and reference:
            del ctx.entries[0]
            del reference[0]
        elif operation == 5:
            ctx.entries *= 0
            reference *= 0
        assert [list(scope.entries) for scope in scopes] == expected
