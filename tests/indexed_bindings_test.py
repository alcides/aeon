"""Indexed bindings preserve mutable-AST, serialization and branching semantics."""

import os
import pickle
import subprocess
import sys

from hypothesis import given, strategies as st

from aeon.core.types import t_bool, t_int
from aeon.typechecking.context import TypingContext, VariableBinder, RefinementBinder, UninterpretedBinder
from aeon.typechecking.context import _BindingIndex
from aeon.utils.name import Name
from aeon.utils.persistent import PersistentMap, PersistentSequence


@given(st.lists(st.tuples(st.integers(0, 20), st.integers(0, 50), st.integers()), max_size=150))
def test_maps_match_branching_ordered_dictionaries(operations):
    maps, dictionaries = [PersistentMap()], [{}]
    for choice, key, value in operations:
        parent = choice % len(maps)
        maps.append(maps[parent].set(key, value))
        dictionaries.append({**dictionaries[parent], key: value})
        for actual, expected in zip(maps, dictionaries):
            assert list(actual.items()) == list(expected.items())
            assert dict(actual) == expected
            assert len(actual) == len(expected)
            assert actual.get(key) == expected.get(key)


def test_colliding_keys_and_source_mutation_do_not_change_siblings():
    class Collision(int):
        def __hash__(self):
            return 0

    source = {Collision(i): [i] for i in range(70)}
    parent = PersistentMap(source)
    left = parent.set(Collision(1), [100])
    right = parent.set(Collision(71), [71])
    source.clear()
    assert left[Collision(1)] == [100]
    assert right[Collision(1)] == parent[Collision(1)] == [1]
    assert Collision(71) not in left and Collision(71) not in parent
    parent[Collision(2)].append(3)
    assert left[Collision(2)] == right[Collision(2)] == [2, 3]


def test_maps_rebuild_hash_buckets_when_deserialized_in_another_process():
    expected = {f"key-{i}": i for i in range(64)}
    mapping = PersistentMap(expected).set("branch", 99)
    payload = pickle.dumps(mapping)
    code = """
import pickle, sys
mapping = pickle.loads(sys.stdin.buffer.read())
expected = {**{f"key-{i}": i for i in range(64)}, "branch": 99}
assert list(mapping.items()) == list(expected.items())
child = mapping.set("branch", 100)
assert child["branch"] == 100 and mapping["branch"] == 99
"""
    # At least one seed differs even if the parent uses a fixed hash seed.
    for seed in ("0", "42"):
        result = subprocess.run(
            [sys.executable, "-c", code],
            input=payload,
            env={**os.environ, "PYTHONHASHSEED": seed},
            capture_output=True,
        )
        assert result.returncode == 0, result.stderr.decode()


@given(st.lists(st.integers(), max_size=200))
def test_sequences_retain_every_prefix(values):
    prefixes = [PersistentSequence()]
    for value in values:
        prefixes.append(prefixes[-1].append(value))
    for length, sequence in enumerate(prefixes):
        assert len(sequence) == length
        assert list(sequence) == values[:length]


def test_index_uses_exact_names_first_binding_and_live_types():
    first = VariableBinder(Name("x", 1), t_int)
    same_text = VariableBinder(Name("x", 2), t_bool)
    ctx = TypingContext([first, same_text]).with_var(Name("x", 1), t_bool)
    assert ctx.type_of(Name("x", 1)) is t_int
    assert ctx.type_of(Name("x", 2)) is t_bool
    first.type = t_bool
    assert ctx.type_of(Name("x", 1)) is t_bool
    assert dict((n.id, ty) for n, ty in ctx.concrete_vars()) == {1: t_bool}


def test_renaming_an_earlier_binder_invalidates_a_cached_positive_lookup():
    first, second = VariableBinder(Name("old", 1), t_int), VariableBinder(Name("new", 2), t_bool)
    parent = TypingContext([first, second]).with_var(Name("a"), t_int)
    child = parent.with_var(Name("b"), t_int)
    assert parent.type_of(second.name) is child.type_of(second.name) is t_bool
    first.name = Name("new", 2)
    assert parent.type_of(second.name) is child.type_of(second.name) is t_int
    first.name.name = "renamed"
    first.name.id = 3
    assert child.type_of(Name("new", 2)) is t_bool
    assert child.type_of(Name("renamed", 3)) is t_int
    assert child.type_of(Name("old", 1)) is None


def test_raw_lists_and_mutated_snapshots_remain_live():
    entries = [VariableBinder(Name("x"), t_int)]
    root = TypingContext(entries)
    child = root.with_var(Name("y"), t_int)
    assert child.type_of(Name("x")) is t_int
    entries[0:0] = [VariableBinder(Name("x"), t_bool)]
    assert root.type_of(Name("x")) is t_bool
    assert child.type_of(Name("x")) is t_int
    child.entries[:] = [UninterpretedBinder(Name("f"), t_int), RefinementBinder(Name("p"), t_bool)]
    assert child.type_of(Name("x")) is None
    assert child.type_of(Name("f")) is t_int
    assert child.type_of(Name("p")) is None
    grandchild = child.with_var(Name("z"), t_bool)
    child.entries.clear()
    assert grandchild.type_of(Name("f")) is t_int


def test_deserialization_rebuilds_indexes_with_stale_names():
    binder = VariableBinder(Name("old"), t_int)
    ctx = TypingContext([binder]).with_var(Name("local"), t_bool)
    assert ctx.type_of(Name("old")) is t_int
    binder.name = Name("new")
    restored = pickle.loads(pickle.dumps(ctx))
    assert restored.type_of(Name("old")) is None
    assert restored.type_of(Name("new")) == t_int


def test_unused_scopes_defer_index_work_and_lookups_extend_only_the_missing_suffix(monkeypatch):
    calls = []
    build, extend = _BindingIndex.build, _BindingIndex.extend

    def counted_build(cls, entries):
        calls.append("build")
        return build(entries)

    def counted_extend(index, binder):
        calls.append("extend")
        return extend(index, binder)

    monkeypatch.setattr(_BindingIndex, "build", classmethod(counted_build))
    monkeypatch.setattr(_BindingIndex, "extend", counted_extend)
    ctx = TypingContext()
    for i in range(100):
        ctx = ctx.with_var(Name("local", i), t_int)
    assert calls == []
    assert ctx.type_of(Name("local", 0)) is t_int
    assert calls == ["build"]
    child = ctx.with_var(Name("child"), t_bool)
    sibling = ctx.with_var(Name("sibling"), t_int)
    assert child.type_of(Name("local", 99)) is t_int
    duplicate = child.with_var(Name("local", 99), t_bool)
    assert duplicate.type_of(Name("local", 99)) is t_int
    assert calls == ["build"]
    assert child.type_of(Name("child")) is t_bool
    assert child.type_of(Name("local", 99)) is t_int
    assert calls == ["build", "extend"]
    assert sibling.type_of(Name("child")) is None
    assert calls == ["build", "extend", "extend"]
