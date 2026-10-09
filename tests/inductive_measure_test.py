"""Regression tests for canonical inductive measure names."""

from aeon.sugar.bind import bind_program
from aeon.sugar.inductives import expand_inductive_decls
from aeon.sugar.parser import parse_program
from aeon.verification.constructor_registry import clear_constructor_registry, get_measures
from aeon.verification.smt import get_sort
from aeon.verification.smt_datatypes import lookup_measure
from aeon.core.types import TypeConstructor
from aeon.utils.name import Name


def test_same_short_measure_name_is_canonicalized_per_inductive():
    """Two ``+ size`` declarations never share a bare SMT/name-resolution alias."""
    source = """
inductive Nat
| zero : {x: Nat | size x = 0}
| succ (n: {n: Nat | size n >= 0}) : {x: Nat | size x = size n + 1}
+ size (n: Nat) : Int

inductive Tree
| leaf : {x: Tree | size x = 1}
| node (left: Tree) (right: Tree) : {x: Tree | size x = size left + size right + 1}
+ size (tree: Tree) : Int
"""
    clear_constructor_registry()
    expanded = expand_inductive_decls(bind_program(parse_program(source), []))

    names = [definition.name.name for definition in expanded.definitions]
    assert "Nat_size" in names
    assert "Tree_size" in names
    assert "size" not in names
    assert get_measures("Nat") == ["Nat_size"]
    assert get_measures("Tree") == ["Tree_size"]

    nat_succ = next(definition for definition in expanded.definitions if definition.name.name == "Nat_succ")
    tree_node = next(definition for definition in expanded.definitions if definition.name.name == "Tree_node")
    assert "Nat_size" in str(nat_succ.type)
    assert "Tree_size" not in str(nat_succ.type)
    assert "Tree_size" in str(tree_node.type)
    assert "Nat_size" not in str(tree_node.type)

    get_sort(TypeConstructor(Name("Nat", 0)))
    get_sort(TypeConstructor(Name("Tree", 0)))
    assert lookup_measure("Nat_size") is not None
    assert lookup_measure("Tree_size") is not None
    assert lookup_measure("size") is None
