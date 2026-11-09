"""Scope snapshots retain list semantics without copying every outer binder."""

import pytest
from hypothesis import given, strategies as st

from aeon.core.types import ArrowKind, Kind, TypeConstructor, TypeVar, t_bool, t_int
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


def test_kind_lookup_reuses_type_binders_without_scanning_term_variables(monkeypatch):
    name = Name("f")
    kind = ArrowKind(Kind.BASE, Kind.BASE)
    ctx = TypingContext().with_typevar(name, kind)
    type_binders = ctx.entries.type_binders()
    for i in range(256):
        ctx = ctx.with_var(Name("x", i), t_int)
    assert ctx.entries.type_binders() is type_binders

    def unexpected_scan(self):
        pytest.fail("Kind lookup must not scan all term variables in a scope")

    monkeypatch.setattr(type(ctx.entries), "__iter__", unexpected_scan)
    assert ctx.kind_of(t_int) == Kind.BASE
    assert ctx.kind_of(TypeVar(name)) == kind
    assert ctx.kind_of(TypeConstructor(name, [t_int])) == Kind.BASE


def test_type_binder_mutations_remain_visible_in_derived_scopes():
    binder = TypeBinder(Name("a"), Kind.BASE)
    parent = TypingContext([binder]).with_var(Name("outer"), t_int)
    child = parent.with_var(Name("inner"), t_int)
    binder.type_name = Name("f")
    binder.type_kind = ArrowKind(Kind.BASE, Kind.BASE)
    assert parent.typevars() == child.typevars() == [(binder.type_name, binder.type_kind)]
    assert child.kind_of(TypeConstructor(binder.type_name, [t_int])) == Kind.BASE
    with pytest.raises(ValueError, match="not in scope"):
        child.kind_of(TypeVar(Name("a")))


@pytest.mark.parametrize("snapshot", [False, True])
@given(st.lists(st.tuples(st.integers(0, 7), st.integers(0, 20)), max_size=60))
def test_type_variable_views_track_mutations_and_scope_extensions(snapshot, operations):
    ctx = TypingContext([TypeBinder(Name("a"), Kind.BASE)])
    if snapshot:
        ctx = ctx.with_var(Name("initial"), t_int)
    for step, (operation, choice) in enumerate(operations):
        before = ctx.typevars()
        child = ctx.with_var(Name("child", step), t_int)
        binder = TypeBinder(Name("a", step), ArrowKind(Kind.BASE, Kind.BASE))
        if operation == 0:
            ctx.entries.append(binder)
        elif operation == 1:
            ctx.entries[:] = [binder]
        elif operation == 2:
            ctx.entries.reverse()
        elif operation == 3 and ctx.entries:
            del ctx.entries[choice % len(ctx.entries)]
        elif operation == 4:
            ctx.entries *= choice % 3
        elif operation == 5:
            ctx.entries.insert(choice, binder)
        elif operation == 6:
            ctx.entries.extend([binder])
        elif operation == 7 and ctx.entries:
            ctx.entries[choice % len(ctx.entries)] = binder
        expected = [(e.type_name, e.type_kind) for e in ctx.entries if isinstance(e, TypeBinder)]
        assert ctx.typevars() == expected
        assert child.typevars() == before
        # Extending a mutated snapshot must retain its current type binders.
        extended = ctx.with_typevar(Name("new", step), Kind.BASE)
        assert extended.typevars() == [*expected, (Name("new", step), Kind.BASE)]


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
