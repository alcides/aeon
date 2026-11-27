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
            "def same : forall a:B, (x:a) -> (y:a) -> a := fun x => fun y => x;\ndef bad : Int := same 1 true;",
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
    assert error.message == "Type mismatch in `reverse tail`: expected Int, got (List Int)."


def test_unification_without_a_source_does_not_invent_an_expression():
    with pytest.raises(UnificationSubtypingError) as raised:
        unify(ElaborationTypingContext(), st_int, st_bool)
    assert raised.value.expr is None
    assert str(raised.value) == "Type mismatch: expected Bool, got Int."


def test_conflicting_inferred_types_explain_the_user_problem():
    source = "def use : forall a:B, (x:a) -> (y:a) -> Int := fun x => fun y => 0;\ndef bad : Int := use 1 true;"
    error = diagnostic(source)
    assert error.range.start.line == 1
    assert error.range.start.character == source.splitlines()[1].index("true")
    assert error.message == (
        "Conflicting types in `true`: Int and Bool.\n"
        "These uses must agree on one type. Check the arguments and branch results."
    )


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
        "Cannot mix a single Int with a list of Int values in `reverse tail`.\n"
        "Conflicting types: Int and (List Int).\n"
        "List.cons adds one element to a list. Use List.append to join two lists."
    )


@pytest.mark.parametrize("reverse", [False, True])
def test_list_element_explanation_does_not_depend_on_constraint_order(reverse):
    types = [st_int, parse_type("List Int")]
    if reverse:
        types.reverse()
    with pytest.raises(UnificationFailedError) as raised:
        unify_single("the union type internal details", types)
    message = str(raised.value)
    assert "Cannot mix a single Int with a list of Int values" in message
    assert "List.cons adds one element" in message
    assert "List.append" in message
    assert "union" not in message
    assert "STypeConstructor" not in message
    assert "SynthesizedLocation" not in message
