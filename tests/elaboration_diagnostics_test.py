"""Type inference must blame source expressions, including deferred constraints."""

import asyncio
import io

import pytest
from lsprotocol.types import DiagnosticSeverity

from aeon.elaboration import unify
from aeon.elaboration.context import ElaborationTypingContext
from aeon.errors import UnificationSubtypingError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp import aeon_adapter
from aeon.sugar.ast_helpers import st_bool, st_int
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
