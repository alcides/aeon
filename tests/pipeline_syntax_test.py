"""Lean application pipelines preserve grouping, types, and refinement checks."""

import pytest
from hypothesis import given, strategies as st

from aeon.errors import TypeApplicationSyntaxError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.parser import mk_parser, parse_expression, parse_type
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.location import FileLocation
from tests.roundtrip_test import structure


@pytest.mark.parametrize(
    "source,ordinary",
    [
        ("f <| g <| x", "f (g x)"),
        ("x |> g |> f", "f (g x)"),
        ("f <| x |> g", "f (g x)"),
        ("x |> f <| y", "(f x) y"),
        ("f a <| g x", "f a (g x)"),
        ("x |> f a", "f a x"),
        ("f <| x + 1", "f (x + 1)"),
        ("x + 1 |> f", "f (x + 1)"),
        ("f <| -1", "f (-1)"),
        ("-1 |> f", "f (-1)"),
        ("f <| -1 |> g", "f (g (-1))"),
        ("f <| if b then x else y", "f (if b then x else y)"),
        ("f <| fun x => x", "f (fun x => x)"),
        ("x |> fun y => y", "(fun y => y) x"),
        ("f <| let x := 1 in x", "f (let x := 1 in x)"),
        ("f $ g <| x", "f (g x)"),
        ("x |> f $ y", "(f x) y"),
        ("f <| x < y", "f (x < y)"),
        ("f <| b || c", "f (b || c)"),
        ("xs |> List.reverse", "List.reverse xs"),
        ("f<|g<|x", "f (g x)"),
        ("x|>g|>f", "f (g x)"),
    ],
)
def test_term_pipeline_grouping(source, ordinary):
    assert structure(parse_expression(source)) == structure(parse_expression(ordinary))


@pytest.mark.parametrize(
    "source,ordinary",
    [
        ("List <| List Int", "List (List Int)"),
        ("List <| List <| Int", "List (List Int)"),
        ("Int |> List |> List", "List (List Int)"),
        ("List <| Int |> List", "List (List Int)"),
        ("Int |> Pair <| Bool", "Pair Int Bool"),
        ("Pair Int <| List Bool", "Pair Int (List Bool)"),
        ("Bool |> Pair Int", "Pair Int Bool"),
        ("(Pair Int) <| Bool", "Pair Int Bool"),
        ("Bool |> (Pair Int)", "Pair Int Bool"),
        ("(Pair Int) Bool", "Pair Int Bool"),
        ("(Pair) Int Bool", "Pair Int Bool"),
        ("Module.Box <| List Int", "Module.Box (List Int)"),
        ("Set <| Bool", "Set Bool"),
        ("Bool |> Set", "Set Bool"),
        ("List <| {v:Int | v >= 5 && v <= 10}", "List {v:Int | v >= 5 && v <= 10}"),
        ("List <| (Duo Int){|r|}", "List ((Duo Int){|r|})"),
        ("List <| (x:Int) -> Int", "List ((x:Int) -> Int)"),
        ("forall a:B, List <| List a", "forall a:B, List (List a)"),
        ("(xs:List <| List Int) -> Int", "(xs:List (List Int)) -> Int"),
        ("{xs:List <| List Int | List.size xs = 0}", "{xs:List (List Int) | List.size xs = 0}"),
    ],
)
def test_type_pipeline_grouping(source, ordinary):
    assert structure(parse_type(source)) == structure(parse_type(ordinary))


@given(
    constructors=st.lists(st.sampled_from(["List", "Box", "Maybe", "Module.Tree"]), min_size=1, max_size=8),
    base=st.sampled_from(["Int", "Bool", "String"]),
)
def test_type_pipeline_chains_match_nested_applications(constructors, base):
    ordinary = base
    for constructor in reversed(constructors):
        ordinary = f"({constructor} {ordinary})"
    expected = structure(parse_type(ordinary))
    assert structure(parse_type(" <| ".join([*constructors, base]))) == expected
    assert structure(parse_type(" |> ".join([base, *reversed(constructors)]))) == expected


@pytest.mark.parametrize("source", ["f <| g x", "x |> g |> f"])
def test_pipeline_source_span(source):
    term = mk_parser("expression", filename="pipes.ae")(source)
    assert term.loc == FileLocation("pipes.ae", (1, 1), (1, len(source) + 1))


def test_non_constructor_type_pipeline_has_a_located_error():
    source = "((x:Int) -> Int) <| Bool"
    with pytest.raises(TypeApplicationSyntaxError) as error:
        mk_parser("type", filename="pipes.ae")(source)
    assert error.value.position() == FileLocation("pipes.ae", (1, 1), (1, len(source) + 1))


@pytest.mark.parametrize(
    "body,value",
    [
        ("3 |> inc |> double", 8),
        ("inc <| double <| 3", 7),
        ("inc <| 3 |> double", 7),
        ("inc <| -1", 0),
        ("-1 |> inc", 0),
    ],
)
def test_term_pipelines_evaluate_and_preserve_refinements(body, value):
    source = f"""
    def inc (x:Int) : {{r:Int | r = x + 1}} := x + 1;
    def double (x:Int) : {{r:Int | r = 2 * x}} := 2 * x;
    def main (u:Int) : {{r:Int | r = {value}}} := {body};
    """
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    assert not list(driver.parse(aeon_code=source))
    assert driver.run() == value
    assert list(driver.parse(aeon_code=source.replace(f"r = {value}}}", f"r = {value + 1}}}")))


def test_nested_lists_typecheck_with_pipelines_in_types_and_terms():
    source = """
    import List;
    def id : forall a:B, (x:a) -> a := Λ a:B => fun x => x;
    def keep (xs:List <| List Int) : List <| List Int := xs;
    def main (u:Int) : Int :=
        let nested:List <| List Int := id{List <| List Int} [[1], [2]];
        nested |> keep |> List.length;
    """
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    assert not list(driver.parse(aeon_code=source))
    assert driver.run() == 2
