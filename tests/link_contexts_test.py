"""Linking preserves scope order, precedence, and ownership of containers."""

from hypothesis import given, strategies as st

from aeon.compilation.link import merge_elab_contexts, merge_metadata, merge_typing_contexts
from aeon.core.types import t_bool, t_int
from aeon.elaboration.context import ElaborationTypingContext, ElabVariableBinder
from aeon.sugar.stypes import STypeConstructor
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.name import Name


@given(st.lists(st.lists(st.integers(0, 8), max_size=12), max_size=6))
def test_typing_merge_preserves_first_binder_and_unions_trust(groups):
    contexts = tuple(
        TypingContext(
            [VariableBinder(Name("x", index), t_int) for index in group],
            trusted_names=frozenset(Name("trusted", index) for index in group),
        )
        for group in groups
    )
    before = [list(ctx.entries) for ctx in contexts]
    extra = Name("explicitly_trusted")
    merged = merge_typing_contexts(contexts, frozenset({extra}))
    expected = list(TypingContext().entries)
    for entries in before:
        for entry in entries:
            if entry not in expected:
                expected.append(entry)
    assert list(merged.entries) == expected
    assert merged.trusted_names == {extra} | {name for ctx in contexts for name in ctx.trusted_names}
    for entry in merged.entries:
        original = next((e for entries in before for e in entries if e == entry), None)
        if original is not None:
            assert entry is original
    merged.entries.clear()
    assert [list(ctx.entries) for ctx in contexts] == before


def test_typing_merge_does_not_deduplicate_by_name_alone():
    name = Name("x")
    first, second = VariableBinder(name, t_int), VariableBinder(name, t_bool)
    merged = merge_typing_contexts((TypingContext([first]), TypingContext([second])))
    assert [entry for entry in merged.entries if isinstance(entry, VariableBinder)] == [first, second]
    assert merged.type_of(name) == t_int


def test_elaboration_merge_retains_shadowing_and_fresh_containers():
    name = Name("x")
    old, new = Name("Old"), Name("New")
    old_type, new_type = STypeConstructor(old), STypeConstructor(new)
    outer = ElaborationTypingContext(
        [ElabVariableBinder(name, old_type)], {"Ctor": old}, {"Ctor": old}, [(name, old_type)]
    )
    inner = ElaborationTypingContext(
        [ElabVariableBinder(name, new_type)], {"Ctor": new}, {"Ctor": new}, [(name, new_type)]
    )
    merged = merge_elab_contexts((outer, inner))
    assert merged.type_of(name) == new_type
    assert merged.entries == [*outer.entries, *inner.entries]
    assert merged.constructor_to_type == {"Ctor": new}
    assert merged.constructor_defs == {"Ctor": new}
    assert merged.instances == [(name, old_type), (name, new_type)]
    merged.entries.clear()
    merged.constructor_to_type.clear()
    merged.constructor_defs.clear()
    merged.instances.clear()
    for ctx, expected_type, expected_name in ((outer, old_type, old), (inner, new_type, new)):
        assert ctx.entries == [ElabVariableBinder(name, expected_type)]
        assert ctx.constructor_to_type == ctx.constructor_defs == {"Ctor": expected_name}
        assert ctx.instances == [(name, expected_type)]


@given(st.lists(st.dictionaries(st.integers(0, 5), st.integers()), max_size=8))
def test_metadata_merge_uses_last_value_without_mutating_inputs(groups):
    parts = [{Name("metadata", key): value for key, value in group.items()} for group in groups]
    before = [dict(part) for part in parts]
    merged = merge_metadata(tuple(parts))
    for key in {key for part in parts for key in part}:
        assert merged[key] == next(part[key] for part in reversed(parts) if key in part)
    assert len(merged) == len({key for part in parts for key in part})
    merged.clear()
    assert parts == before


def test_empty_merges():
    assert merge_typing_contexts(()).entries == TypingContext().entries
    assert merge_typing_contexts(()).trusted_names == frozenset()
    assert merge_elab_contexts(()) == ElaborationTypingContext()
    assert merge_metadata(()) == {}
