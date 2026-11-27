"""Type inference must blame source expressions, including deferred constraints."""

import asyncio
import io

import pytest
from lsprotocol.types import DiagnosticSeverity

from aeon.elaboration import unify, unify_single
from aeon.elaboration.context import ElaborationTypingContext
from aeon.errors import UnificationFailedError, UnificationSubtypingError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp import aeon_adapter
from aeon.sugar.ast_helpers import st_bool, st_int
from aeon.sugar.parser import parse_type
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.pprint import pretty_print_stype


def diagnostic(source):
    uri = "file:///elaboration-diagnostic.ae"
    aeon_adapter.clear_cache(uri)
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
    result = asyncio.run(aeon_adapter._parse(io.StringIO(source), driver, uri))
    errors = [d for d in result.diagnostics if d.severity == DiagnosticSeverity.Error]
    assert len(errors) == 1, errors
    return errors[0]


@pytest.mark.parametrize(
    "source,expression,expected,actual",
    [
        ("def bad : Int := true;", "true", "Int", "Bool"),
        (
            "def take (value:Int) : Int := value;\ndef bad : Int := take true;",
            "true",
            "Int",
            "Bool",
        ),
        (
            "def bad (value:Int) : Bool := value;",
            "value",
            "Bool",
            "Int",
        ),
        (
            "def same : forall a:B, (x:a) -> (y:a) -> a := Λ a:B => fun x => fun y => x;\ndef bad : Int := same 1 true;",
            "true",
            "Int",
            "Bool",
        ),
        (
            "def take (value:Int) : Int := value;\ndef bad : Int := take (if true then 1 else false);",
            "false",
            "Int",
            "Bool",
        ),
        (
            "def use (f:(value:Int) -> Int) : Int := f 1;\ndef bad : Int := use (fun value => true);",
            "fun value => true",
            "Int",
            "Bool",
        ),
    ],
)
def test_mismatch_names_the_source_expression(source, expression, expected, actual):
    error = diagnostic(source)
    line = source.splitlines()[-1]
    column = line.rindex(expression)
    assert error.range.start.line == len(source.splitlines()) - 1
    assert error.range.start.character == column
    assert error.range.end.character == column + len(expression)
    if error.message.startswith("Type parameter"):
        assert f"- {expected} required" in error.message
        assert f"- {actual} required" in error.message
        assert f"by `{expression}`" in error.message
    else:
        assert f"expected {expected}" in error.message
        assert f"in `{expression}`" in error.message
        assert f"got {actual}" in error.message
    assert "todo" not in error.message
    assert "()" not in error.message


def test_deferred_match_constraint_blames_the_bad_constructor_argument():
    source = """import List;

def reverse (xs:List Int) : {r:List Int |
  (List.structuralRank xs = 0 --> r = empty) &&
  (List.structuralRank xs > 0 -->
    r = append (reverse (List.rest xs)) (List.cons (List.first xs) empty))}
  decreasing_by [List.structuralRank xs] :=
  match xs with
  | nil => List.nil
  | cons x tail => List.cons (reverse tail) (List.cons x List.nil);
"""
    error = diagnostic(source)
    line = source.splitlines()[9]
    column = line.index("reverse tail")
    assert error.range.start.line == 9
    assert error.range.end.line == 9
    assert error.range.start.character == column
    assert error.range.end.character == column + len("reverse tail")
    assert error.message.startswith("Type parameter `a` in `List.cons` must be both (List Int) and Int.")
    assert "(List Int) required by `reverse tail`" in error.message
    assert "one consistent type within an application" in error.message


def test_unification_without_a_source_does_not_invent_an_expression():
    with pytest.raises(UnificationSubtypingError) as raised:
        unify(ElaborationTypingContext(), st_int, st_bool)
    assert raised.value.expr is None
    assert str(raised.value) == "Type mismatch: expected Bool, got Int."


def test_conflicting_inferred_types_explain_the_user_problem():
    source = (
        "def use : forall a:B, (x:a) -> (y:a) -> Int := Λ a:B => fun x => fun y => 0;\ndef bad : Int := use 1 true;"
    )
    error = diagnostic(source)
    assert error.range.start.line == 1
    assert error.range.start.character == source.splitlines()[1].index("true")
    assert error.message == (
        "Type parameter `a` in `use` must be both Int and Bool.\n"
        "- Int required by `1` at elaboration-diagnostic.ae:2:22.\n"
        "- Bool required by `true` at elaboration-diagnostic.ae:2:24.\n"
        "A type parameter must have one consistent type within an application. "
        "Check the argument types, type annotations, and explicit type arguments."
    )
    assert len(error.related_information) == 2
    assert [related.location.range.start.character for related in error.related_information] == [21, 23]


def test_conflict_in_induction_proof_points_to_the_list_argument():
    source = """import List;


def reverse (xs:List Int) : {r:List Int |
  (List.structuralRank xs = 0 --> r = empty) &&
  (List.structuralRank xs > 0 -->
    r = append (reverse (List.rest xs)) (List.cons (List.first xs) empty))}
  decreasing_by [List.structuralRank xs] :=
  match xs with
  | nil => List.nil
  | cons x tail => List.append (reverse tail) (List.cons x List.nil);

theorem reverse_size (xs:List Int) : List.size (reverse xs) = List.size xs := by
  induction xs with
  | nil => smt
  | cons x tail ih =>
    calc
      List.size (reverse xs) = List.size (List.cons (reverse tail) (List.cons{Int}{|fun value => true|} x List.nil)) := by smt
      _ = List.size tail + 1 := by simp [ih]
      _ = List.size xs := by smt
"""
    error = diagnostic(source)
    column = source.splitlines()[17].index("reverse tail")
    assert error.range.start.line == error.range.end.line == 17
    assert error.range.start.character == column
    assert error.range.end.character == column + len("reverse tail")
    assert error.message == (
        "Type parameter `a` in `List.cons` must be both Int and (List Int).\n"
        "- Int required by `List.cons{Int}` at elaboration-diagnostic.ae:18:69.\n"
        "- (List Int) required by `reverse tail` at elaboration-diagnostic.ae:18:54.\n"
        "A type parameter must have one consistent type within an application. "
        "Check the argument types, type annotations, and explicit type arguments."
    )


@pytest.mark.parametrize("reverse", [False, True])
@pytest.mark.parametrize(
    "first,second",
    [("Int", "Bool"), ("Int", "List Int"), ("Crate Int", "Crate Bool"), ("(x:Int)->Int", "(x:Bool)->Int")],
)
def test_type_conflict_explanation_is_independent_of_type_shape_and_order(first, second, reverse):
    types = [parse_type(first), parse_type(second)]
    if reverse:
        types.reverse()
    with pytest.raises(UnificationFailedError) as raised:
        unify_single("the union type internal details", types)
    message = str(raised.value)
    assert all(pretty_print_stype(ty) in message for ty in types)
    assert "All uses of an inferred type must agree" in message
    assert "List.cons" not in message
    assert "List.append" not in message
    assert "union" not in message
    assert "STypeConstructor" not in message
    assert "SynthesizedLocation" not in message


@pytest.mark.parametrize(
    "declarations,application,parameter,first,second,first_source,second_source",
    [
        (
            "inductive Crate a | wrap (value:a) : (Crate a)\n"
            "def use : forall element:B, (x:element) -> (y:element) -> Int := Λ element:B => fun x => fun y => 0;\n",
            "use (Crate.wrap 1) (Crate.wrap true)",
            "element",
            "(Crate Int)",
            "(Crate Bool)",
            "Crate.wrap 1",
            "Crate.wrap true",
        ),
        (
            "def use : forall element:B, (x:element) -> (y:element) -> Int := Λ element:B => fun x => fun y => 0;\n"
            "def first (x:Int):Int := 0;\ndef second (y:Bool):Int := 0;\n",
            "use first second",
            "element",
            "(x : Int) → Int",
            "(y : Bool) → Int",
            "first",
            "second",
        ),
        (
            "inductive Crate a | wrap (value:a) : (Crate a)\n"
            "inductive Parcel a | pack (value:a) : (Parcel a)\n"
            "def use : forall f:B -> B, (x:f Int) -> (y:f Int) -> Int := Λ f:B -> B => fun x => fun y => 0;\n",
            "use (Crate.wrap 1) (Parcel.pack 1)",
            "f",
            "Crate",
            "Parcel",
            "Crate.wrap 1",
            "Parcel.pack 1",
        ),
    ],
)
def test_polymorphic_context_supports_custom_types_functions_and_higher_kinds(
    declarations, application, parameter, first, second, first_source, second_source
):
    source = declarations + f"def bad:Int := {application};"
    error = diagnostic(source)
    assert error.message.startswith(f"Type parameter `{parameter}` in `use` must be both {first} and {second}.")
    assert f"{first} required by `{first_source}`" in error.message
    assert f"{second} required by `{second_source}`" in error.message
    assert len(error.related_information) == 2
    assert all(related.location.uri == "file:///elaboration-diagnostic.ae" for related in error.related_information)
    assert "List.cons" not in error.message
    assert "List.append" not in error.message


def test_separate_polymorphic_applications_can_choose_different_types():
    source = (
        "def use : forall element:B, (x:element) -> (y:element) -> Int := Λ element:B => fun x => fun y => 0;\n"
        "def numbers : Int := use 1 2;\ndef booleans : Int := use true false;"
    )
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
    assert not list(driver.parse(aeon_code=source))
