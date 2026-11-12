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
        (
            "let n := Array.length arr in let 1 updated := Array.set arr (n - 1) 7 in (Array.consume Array.sum) updated",
            12,
        ),
        ("let n := Array.length arr + Array.length arr in n + (Array.consume Array.sum) arr", 18),
        ("let b := Array.empty arr in if b then (Array.consume Array.sum) arr else (Array.consume Array.sum) arr", 14),
        ("let n := if true then Array.length arr else 0 in n + (Array.consume Array.sum) arr", 16),
        ("let n := Array.length arr in let done := Array.dispose arr in n", 2),
        ("let reader := Array.length in let n := reader arr in n + (Array.consume Array.sum) arr", 16),
        ("let 1 other := arr in let n := Array.length arr in n + (Array.consume Array.sum) other", 16),
    ],
)
def test_borrow_then_consume(body, expected):
    driver, errors = compile_source(f"def main (_:Int):Int := let 1 arr := #[5,9] in {body};")
    assert not errors, errors
    assert driver.run() == expected


@pytest.mark.parametrize(
    "body",
    [
        "let n := (Array.consume Array.sum) arr in Array.length arr",
        "let 1 updated := Array.set arr 0 7 in let n := Array.length arr in n + (Array.consume Array.sum) updated",
        "let 1 other := arr in let n := (Array.consume Array.sum) other in Array.length arr",
        "let 1 other := arr in let n := (Array.consume Array.sum) arr in Array.length other",
        "let n := if true then (Array.consume Array.sum) arr else (Array.consume Array.sum) arr in Array.length arr",
        "let reader:(x:Int) -> Int := fun x => Array.length arr in let n := (Array.consume Array.sum) arr in reader 0",
        "let reader:(x:Int) -> Int := fun x => Array.length arr in reader 0",
        "(Array.consume Array.sum) (Array.set arr (Array.length arr - 1) 7)",
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
        "def bad (borrow arr:(Array Int)):Int := (Array.consume Array.sum) arr;",
        "def bad (borrow arr:(Array Int)):(Array Int) := arr;",
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
            let n := observe (Array.consume Array.sum) arr in
            n + (Array.consume Array.sum) arr;
    """)
    assert errors


def test_borrowing_function_can_be_passed_to_a_borrowing_callback():
    driver, errors = compile_source("""
        def observe (f:(borrow xs:(Array Int)) -> Int) (borrow arr:(Array Int)):Int := f arr;
        def main (_:Int):Int :=
            let 1 arr := #[5,9] in
            let n := observe Array.length arr in
            n + (Array.consume Array.sum) arr;
    """)
    assert not errors, errors
    assert driver.run() == 16


def test_opaque_borrower_signature_can_return_fresh_storage():
    arr = TypeConstructor(Name("Array"), [t_int])
    signature = AbstractionType(Name("arr"), arr, arr, multiplicity=MBorrow)
    ctx = TypingContext().with_var(Name("leak"), signature)
    # The implementation must establish independence. As with refinements,
    # imported/native function bodies are a trusted boundary.
    assert not check_linearity(Literal(0, t_int), ctx)


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


def test_owned_first_parameter_can_be_read_inside_a_curried_function():
    driver, errors = compile_source("""
        def update (1 arr:{a:(Array Int) | Array.size a > 0}) (value:Int):Int :=
            let n := Array.length arr in
            let 1 updated := Array.set arr (n - 1) value in
            Array.consume Array.sum updated;
        def main (_:Int):Int := update #[1,2] 7;
    """)
    assert not errors, errors
    assert driver.run() == 8


def test_two_borrowed_arguments_and_repeated_element_reads():
    driver, errors = compile_source("""
        def same (borrow left:(Array Int)) (borrow right:(Array Int)):Bool :=
            Array.length left = Array.length right;
        def main (_:Int):Int :=
            let 1 arr := #[5,9] in
            let equal := same arr arr in
            let first := Array.get arr 0 in
            let 1 updated := Array.set arr 0 (first + 1) in
            let result := if equal then Array.get updated 0 else 0 in
            let _ := Array.dispose updated in result;
    """)
    assert not errors, errors
    assert driver.run() == 6


@pytest.mark.parametrize(
    "body",
    [
        "let at := Array.get arr in let _ := Array.dispose arr in at 0",
        "let update := Array.set arr in Array.consume Array.sum (update 0 3)",
        "let f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in f 0 + f 1",
        "read arr (let _ := Array.dispose arr in 0)",
    ],
)
def test_retained_partial_calls_and_moves_during_later_arguments_are_rejected(body):
    _, errors = compile_source(f"""
        def read (borrow arr:(Array Int)) (index:Int):Int := Array.length arr + index;
        def main (_:Int):Int := let 1 arr := #[5,9] in {body};
    """)
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_pure_borrower_can_allocate_independent_owned_result():
    driver, errors = compile_source("""
        def sizes (borrow arr:(Array Int)):{xs:(Array Int) | Array.size xs = 1} := #[Array.length arr];
        def main (_:Int):Int :=
            let 1 arr := #[5,9] in
            let 1 result := sizes arr in
            let _ := Array.dispose arr in
            Array.take result 0;
    """)
    assert not errors, errors
    assert driver.run() == 2


def test_copy_does_not_duplicate_nested_owned_elements():
    _, errors = compile_source("""
        def main (_:Int):Int :=
            let 1 pair := Array.copy #[#[1,2]] in
            Array.with_pair pair (fun left => fun right =>
                let _ := Array.dispose left in
                let _ := Array.dispose right in 0);
    """)
    assert errors
    assert any("Copy" in str(error) for error in errors), errors


def test_copyable_scalar_copy_has_independent_storage():
    driver, errors = compile_source("""
        def main (_:Int):Int :=
            Array.with_pair (Array.copy #[1,2]) (fun left => fun right =>
                let 1 updated := Array.set left 0 7 in
                let value := Array.get right 0 in
                let _ := Array.dispose updated in
                let _ := Array.dispose right in value);
    """)
    assert not errors, errors
    assert driver.run() == 1


@pytest.mark.parametrize("last,valid", [(7, True), (8, False)])
def test_borrowed_read_matches_dictionary_free_logical_specification(last, valid):
    driver, errors = compile_source(f"""
        def data (_:Unit):{{a:(Array Int) | Array.size a = 2}} := #[3,7];
        def main (_:Int):{{v:Int | v = Array.get (data unit) 1}} :=
            Array.get #[3,{last}] 1;
    """)
    assert (not errors) == valid
    if valid:
        assert driver.run() == 7


def test_sys_argv_returns_independent_owned_arrays(monkeypatch):
    import sys

    monkeypatch.setattr(sys, "argv", ["original"])
    driver, errors = compile_source("""
        import Sys;
        def main (_:Int):String :=
            let 1 left := Sys.argv unit in
            let 1 right := Sys.argv unit in
            if Array.length left > 0 && Array.length right > 0 then
                let 1 changed := Array.set left 0 "changed" in
                let result := Array.get right 0 in
                let _ := Array.dispose changed in
                let _ := Array.dispose right in result
            else
                let _ := Array.dispose left in
                let _ := Array.dispose right in "empty";
    """)
    assert not errors, errors
    assert driver.run() == "original"
    assert sys.argv == ["original"]


def test_inline_one_use_callback_can_move_an_outer_owner():
    driver, errors = compile_source("""
        def main (_:Int):Int :=
            let 1 extra := #[3] in
            Array.with_pair (Array.copy #[1,2]) (fun left => fun right =>
                let total := Array.sum extra + Array.sum left + Array.sum right in
                let _ := Array.dispose extra in
                let _ := Array.dispose left in
                let _ := Array.dispose right in total);
    """)
    assert not errors, errors
    assert driver.run() == 9


def test_one_use_callback_cannot_return_a_retained_resource_closure():
    _, errors = compile_source("""
        def keep (1 f:(x:Int) -> Int):(x:Int) -> Int := f;
        def main (_:Int):Int :=
            let 1 arr := #[1,2] in
            let f := keep (fun x => Array.consume Array.sum arr) in
            f 0 + f 1;
    """)
    assert any(isinstance(error, LinearityError) for error in errors), errors
