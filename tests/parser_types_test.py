"""Type applications accept optional outer parentheses while preserving grouping."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.parser import parse_type
from aeon.sugar.stypes import STypeConstructor
from aeon.synthesis.uis.api import SilentSynthesisUI
from tests.roundtrip_test import structure


@pytest.mark.parametrize(
    "source,parenthesized",
    [
        ("List Int", "(List Int)"),
        ("Array Bool", "(Array Bool)"),
        ("Module.Box Int", "(Module.Box Int)"),
        ("Pair Int Bool", "(Pair Int Bool)"),
        ("List (List Int)", "(List (List Int))"),
        ("Pair (List Int) (Array Bool)", "(Pair (List Int) (Array Bool))"),
        ("List {v:Int | v >= 5 && v <= 10}", "(List {v:Int | v >= 5 && v <= 10})"),
        ("{xs:List Int | List.size xs = 0}", "{xs:(List Int) | List.size xs = 0}"),
        ("(xs:List Int) -> List Int", "(xs:(List Int)) -> (List Int)"),
        ("(borrow xs:List Int) -> Int", "(borrow xs:(List Int)) -> Int"),
        ("forall a:B, List a", "forall a:B, (List a)"),
        ("List ((x:Int) -> Int)", "(List ((x:Int) -> Int))"),
        ("List (x:Int) -> Int", "(List (x:Int) -> Int)"),
        ("List (forall a:B, (x:a) -> a)", "(List (forall a:B, (x:a) -> a))"),
        ("List forall a:B, (x:a) -> a", "(List forall a:B, (x:a) -> a)"),
        ("forall <p:List Int -> Bool>, Int", "forall <p:(List Int) -> Bool>, Int"),
        ("List (Duo Int){|r|}", "(List (Duo Int){|r|})"),
        ("(Duo Int){|r|}{|s|}", "((Duo Int){|r|}){|s|}"),
    ],
)
def test_type_application_parentheses_are_optional(source, parenthesized):
    assert structure(parse_type(source)) == structure(parse_type(parenthesized))


def test_type_application_does_not_absorb_sibling_arguments():
    ty = parse_type("Pair Int Bool")
    assert isinstance(ty, STypeConstructor)
    assert ty.name.name == "Pair"
    assert [arg.name.name for arg in ty.args] == ["Int", "Bool"]


@pytest.mark.parametrize("element_type", ["List Int", "(List Int)"])
@pytest.mark.parametrize("predicate,valid", [("xs = List.nil && List.size xs = 0", True), ("List.size xs = 1", False)])
def test_empty_list_refinement_checks_with_either_spelling(element_type, predicate, valid):
    source = f"""
    import List;
    def empty : {{xs:{element_type} | {predicate}}} := List.nil;
    """
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True, check_only=True))
    assert (not list(driver.parse(aeon_code=source))) == valid


def test_bare_types_in_declarations_binders_and_explicit_instantiation():
    source = """
    import List;
    import Array;
    inductive Pair a b
    | pair (first:a) (second:b) : Pair a b
    def id : forall a:B, (x:a) -> a := Λ a:B => fun x => x;
    def keep (xs:List Int) : List Int := xs;
    def lists : List (List Int) := [[1, 2]];
    def arrays (u:Int) : Array Int := #[1, 2];
    def main (args:Int) : Int :=
        let xs:List Int := id{List Int} (keep [1, 2, 3]);
        let p:Pair (List Int) Bool := Pair.pair xs true;
        match p with | pair values flag => List.length values;
    """
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    assert not list(driver.parse(aeon_code=source))
    assert driver.run() == 3
