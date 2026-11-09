"""Coherent instance resolution, superclass evidence, and checked contracts."""

import pytest

from aeon.errors import TypeClassError, InstanceResolutionError
from tests.typeclass_test import _run, _errors


EQ = """
class Eq (a:B) where
    eq : (x:a) -> (y:a) -> Bool;
"""
INT_EQ = """
instance : Eq Int where
    eq x y := x = y;
"""
ORDER = """
class Order (a:B) extends (Eq a) where
    lt : (x:a) -> (y:a) -> Bool;
"""
INT_ORDER = """
instance : Order Int where
    lt x y := x < y;
"""


def test_generic_constraint_supplies_method():
    assert (
        _run(
            EQ
            + INT_EQ
            + """
    def same [Eq a] (x:a) (y:a) : Bool := eq x y;
    def main (args:Int) : Bool := same 3 3;
    """
        )
        is True
    )


def test_superclass_dictionary_is_available_in_generic_function():
    # Declaration order does not change superclass requirements.
    assert (
        _run(
            EQ
            + ORDER
            + INT_ORDER
            + INT_EQ
            + """
    def same [Order a] (x:a) (y:a) : Bool := eq x y;
    def main (args:Int) : Bool := same 3 3;
    """
        )
        is True
    )


def test_missing_superclass_is_rejected():
    errors = _errors(EQ + ORDER + INT_ORDER + "def main (args:Int) : Bool := lt 1 2;")
    assert any(isinstance(e, InstanceResolutionError) for e in errors)


def test_transitive_superclass():
    assert (
        _run(
            EQ
            + ORDER
            + """
    class Ranked (a:B) extends (Order a) where
        rank : (x:a) -> Int;
    """
            + INT_EQ
            + INT_ORDER
            + """
    instance : Ranked Int where
        rank x := x;
    def same [Ranked a] (x:a) (y:a) : Bool := eq x y;
    def main (args:Int) : Bool := same 3 4;
    """
        )
        is False
    )


@pytest.mark.parametrize(
    "declarations",
    [
        "class A (a:B) extends (Missing a) where m : (x:a) -> a;",
        "class A (a:B) extends (A a) where m : (x:a) -> a;",
        "class A (a:B) extends (B a) where m : (x:a) -> a; class B (a:B) extends (A a) where n : (x:a) -> a;",
    ],
)
def test_invalid_superclasses_report_typeclass_error(declarations):
    assert any(isinstance(e, TypeClassError) for e in _errors(declarations + "def main (args:Int) : Int := 0;"))


def test_all_instance_arguments_participate_in_dispatch():
    assert (
        _run("""
    class Pick (a:B) (b:B) where
        pick : (x:a) -> (y:b) -> a;
    instance : Pick Int Bool where
        pick x y := x;
    instance : Pick Int Int where
        pick x y := y;
    def main (args:Int) : Int := pick 3 true + pick 7 8;
    """)
        == 11
    )


def test_nested_arguments_participate_in_dispatch():
    assert (
        _run("""
    inductive Box a
    | box (value:a) : (Box a)
    class Tag (a:B) where
        tag : (x:a) -> Int;
    instance : Tag (Box Int) where
        tag x := 1;
    instance : Tag (Box Bool) where
        tag x := 2;
    def main (args:Int) : Int := tag (Box.box 3) + tag (Box.box true);
    """)
        == 3
    )


@pytest.mark.parametrize(
    "second",
    [
        "instance duplicate : Eq Int where eq x y := false;",
        "instance general : Eq a where eq x y := true;",
    ],
)
def test_overlaps_are_rejected_even_if_unused(second):
    errors = _errors(EQ + INT_EQ + second + "def main (args:Int) : Int := 0;")
    assert any(isinstance(e, TypeClassError) and "Overlapping" in str(e) for e in errors)


def test_repeated_instance_variables_match_structurally():
    errors = _errors("""
    inductive Box a
    | box (value:a) : (Box a)
    class Same (a:B) (b:B) where
        same : (x:a) -> (y:b) -> Bool;
    instance : Same a a where
        same x y := true;
    def main (args:Int) : Bool := same (Box.box 3) (Box.box true);
    """)
    assert any(isinstance(e, InstanceResolutionError) for e in errors)


def test_nonterminating_instance_requirements_report_error():
    errors = _errors(
        EQ
        + """
    instance [Eq a] : Eq a where
        eq x y := true;
    def main (args:Int) : Bool := eq 3 3;
    """
    )
    assert any(isinstance(e, TypeClassError) and "Non-terminating" in str(e) for e in errors)


@pytest.mark.parametrize("expression,result", [("add 3 4", 7), ("sub 9 2", 7), ("mul 3 4", 12)])
def test_numeric_method_contracts_reach_callers(expression, result):
    assert _run(f"open Num; def main (args:Int) : {{r:Int | r = {result}}} := {expression};") == result


def test_numeric_contract_rejects_incorrect_claim():
    assert _errors("open Num; def main (args:Int) : {r:Int | r = 8} := add 3 4;")


def test_generic_numeric_contract():
    assert (
        _run("""
    open Num
    def twice [Num a] (x:a) : {r:a | r = x + x} := add x x;
    def main (args:Int) : {r:Int | r = 10} := twice 5;
    """)
        == 10
    )


def test_multiple_superclasses_supply_both_dictionaries():
    assert (
        _run(
            EQ
            + INT_EQ
            + """
    class Render (a:B) where
        render : (x:a) -> Int;
    class Key (a:B) extends (Eq a), (Render a) where
        key : (x:a) -> Int;
    instance : Render Int where
        render x := x;
    instance : Key Int where
        key x := x;
    def compareKeys [Key a] (x:a) (y:a) : Int := if eq x y then render x else 0;
    def main (args:Int) : Int := compareKeys 7 7;
    """
        )
        == 7
    )


def test_instance_must_satisfy_method_contract():
    assert _errors("""
    class ExactEq (a:B) where
        exactEq : (x:a) -> (y:a) -> {r:Bool | r = (x = y)};
    instance : ExactEq Int where
        exactEq x y := false;
    def main (args:Int) : Int := 0;
    """)


def test_function_instance_heads_match_the_whole_signature():
    assert (
        _run("""
    class Tag (a:*) where
        tag : (x:a) -> Int;
    instance : Tag ((x:Int) -> Int) where
        tag f := 1;
    instance : Tag ((x:Bool) -> Int) where
        tag f := 2;
    def main (args:Int) : Int :=
        tag (fun x => x + 1) + tag (fun x => if x then 1 else 0);
    """)
        == 3
    )


def test_named_instances_cannot_shadow_each_other():
    errors = _errors(
        EQ
        + """
    instance shared : Eq Int where eq x y := x = y;
    instance shared : Eq Bool where eq x y := x = y;
    def main (args:Int) : Int := 0;
    """
    )
    assert any(isinstance(e, TypeClassError) and "Duplicate instance name" in str(e) for e in errors)
