"""Borrowed reads keep the unique owner alive until its consuming use."""

import pytest

from aeon.core.multiplicity import M1, MBorrow
from aeon.core.terms import Literal
from aeon.core.types import AbstractionType, TypeConstructor, t_int
from aeon.errors import BorrowingError, LinearityError, LinearUnusedError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.linearity import check_linearity
from aeon.utils.name import Name
from aeon.verification.sub import cfalse, sub


def compile_source(source):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(driver.parse(aeon_code="import Array;\n" + source))
    return driver, errors


@pytest.mark.parametrize(
    "body,expected",
    [
        ("let n := Array.length arr in let 1 updated := Array.set arr (n - 1) 7 in Array.sum updated", 12),
        ("let n := Array.length arr + Array.length arr in n + Array.sum arr", 18),
        ("let b := Array.empty arr in if b then Array.sum arr else Array.sum arr", 14),
        ("let n := if true then Array.length arr else 0 in n + Array.sum arr", 16),
        ("let n := Array.length arr in let done := Array.dispose arr in n", 2),
        ("let reader := Array.length in let n := reader arr in n + Array.sum arr", 16),
        ("let 1 other := arr in let n := Array.length arr in n + Array.sum other", 16),
    ],
)
def test_borrow_then_consume(body, expected):
    driver, errors = compile_source(f"def main (_:Int):Int := let 1 arr := #[5,9] in {body};")
    assert not errors, errors
    assert driver.run() == expected


@pytest.mark.parametrize(
    "body",
    [
        "let n := Array.sum arr in Array.length arr",
        "let 1 updated := Array.set arr 0 7 in let n := Array.length arr in n + Array.sum updated",
        "let 1 other := arr in let n := Array.sum other in Array.length arr",
        "let 1 other := arr in let n := Array.sum arr in Array.length other",
        "let n := if true then Array.sum arr else Array.sum arr in Array.length arr",
        "let reader:(x:Int) -> Int := fun x => Array.length arr in let n := Array.sum arr in reader 0",
        "let reader:(x:Int) -> Int := fun x => Array.length arr in reader 0",
        "Array.sum (Array.set arr (Array.length arr - 1) 7)",
    ],
)
def test_read_after_move_or_escaping_capture_is_rejected(body):
    _, errors = compile_source(f"def main (_:Int):Int := let 1 arr := #[5,9] in {body};")
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_borrow_does_not_discharge_ownership():
    _, errors = compile_source("def main (_:Int):Int := let 1 arr := #[5,9] in Array.length arr;")
    assert any(isinstance(error, LinearUnusedError) for error in errors), errors


def test_user_defined_borrower_preserves_length_refinement():
    driver, errors = compile_source("""
        def read (borrow arr:(Array a)):{n:Int | n = Array.size arr} := Array.length arr;
        def main (_:Int):{n:Int | n = 2} :=
            let 1 arr := #[5,9] in
            let n := read arr in
            let 1 updated := Array.set arr (n - 1) 7 in
            let after := read updated in
            let done := Array.dispose updated in
            after;
    """)
    assert not errors, errors
    assert driver.run() == 2


@pytest.mark.parametrize(
    "definition",
    [
        "def bad (borrow arr:(Array Int)):Int := Array.sum arr;",
        "def bad (borrow arr:(Array Int)):(Array Int) := arr;",
        'def bad (borrow arr:(Array Int)):(Array Int) := native "arr";',
        "def bad (borrow arr:(Array Int)):(x:Int) -> Int := fun x => Array.length arr;",
    ],
)
def test_borrowed_parameter_cannot_move_or_escape(definition):
    _, errors = compile_source(definition + "\ndef main (_:Int):Int := 0;")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


def test_consuming_function_cannot_be_used_as_a_borrower():
    _, errors = compile_source("""
        def observe (f:(borrow xs:(Array Int)) -> Int) (borrow arr:(Array Int)):Int := f arr;
        def main (_:Int):Int :=
            let 1 arr := #[5,9] in
            let n := observe Array.sum arr in
            n + Array.sum arr;
    """)
    assert errors


def test_borrowing_function_can_be_passed_to_a_borrowing_callback():
    driver, errors = compile_source("""
        def observe (f:(borrow xs:(Array Int)) -> Int) (borrow arr:(Array Int)):Int := f arr;
        def main (_:Int):Int :=
            let 1 arr := #[5,9] in
            let n := observe Array.length arr in
            n + Array.sum arr;
    """)
    assert not errors, errors
    assert driver.run() == 16


def test_opaque_context_borrower_cannot_return_an_alias():
    arr = TypeConstructor(Name("Array"), [t_int])
    signature = AbstractionType(Name("arr"), arr, arr, multiplicity=MBorrow)
    ctx = TypingContext().with_var(Name("leak"), signature)
    assert any(isinstance(error, BorrowingError) for error in check_linearity(Literal(0, t_int), ctx))


def test_core_subtyping_preserves_borrow_qualifiers():
    consuming = AbstractionType(Name("x"), t_int, t_int, multiplicity=M1)
    borrowing = AbstractionType(Name("x"), t_int, t_int, multiplicity=MBorrow)
    assert sub(TypingContext(), consuming, borrowing) == cfalse
    assert sub(TypingContext(), borrowing, consuming) == cfalse


def test_borrowed_length_is_a_snapshot_before_native_mutation():
    driver, errors = compile_source("""
        def push (1 arr:(Array Int)) (x:Int):
            {r:(Array Int) | Array.size r = Array.size arr + 1} := native "arr.append(x) or arr";
        def main (_:Int):{delta:Int | delta = 1} :=
            let 1 arr := #[5,9] in
            let before := Array.length arr in
            let 1 updated := push arr 7 in
            let after := Array.length updated in
            let _ := Array.dispose updated in
            after - before;
    """)
    assert not errors, errors
    assert driver.run() == 1
