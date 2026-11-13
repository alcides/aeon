"""Borrowed closure environments live inside inferred lexical scopes."""

import pytest

from aeon.errors import BorrowingError, LinearityError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_source(source, *, contracts=False):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, contracts=contracts))
    errors = list(driver.parse(aeon_code="import Array;\n" + source))
    return driver, errors


@pytest.mark.parametrize("contracts", [False, True])
@pytest.mark.parametrize(
    "observation,expected",
    [
        ("let read := Array.get arr in read 0 + read 1", 14),
        ("let read:(i:Int) -> Int := fun i => Array.length arr + i in read 0 + read 1", 5),
        ("let read := Array.get arr in let alias := read in alias 0 + read 1", 14),
        (
            "let read := Array.get arr in let again:(i:{j:Int | j >= 0 && j < 2}) -> Int := fun i => read i in again 0 + again 1",
            14,
        ),
        ("let 1 read := Array.get arr in read 0", 5),
        (
            "let read:(i:{j:Int | j >= 0 && j < 2}) -> Int := if true then Array.get arr else Array.get arr in read 0 + read 1",
            14,
        ),
    ],
)
def test_scoped_borrow_ends_before_owner_is_consumed(observation, expected, contracts):
    driver, errors = compile_source(
        f"""
def main (_:Int):Int :=
    let 1 arr := #[5,9] in
    let n := ({observation}) in
    let _ := Array.dispose arr in n;
""",
        contracts=contracts,
    )
    assert not errors, errors
    assert driver.run() == expected


@pytest.mark.parametrize("callback", ["Array.get arr", "fun i => Array.length arr + i"])
@pytest.mark.parametrize("contracts", [False, True])
def test_borrow_callback_can_be_invoked_repeatedly(callback, contracts):
    driver, errors = compile_source(
        f"""
def twice (borrow f:(i:{{j:Int | j >= 0 && j < 2}}) -> Int):Int := let alias := f in alias 0 + f 1;
def main (_:Int):Int :=
    let 1 arr := #[5,9] in
    let n := twice ({callback}) in
    let _ := Array.dispose arr in n;
""",
        contracts=contracts,
    )
    assert not errors, errors
    assert driver.run() == (14 if callback.startswith("Array.get") else 5)


@pytest.mark.parametrize(
    "body",
    [
        "let read := Array.get arr in let _ := Array.dispose arr in read 0",
        "let read := Array.get arr in let n := read 0 in let _ := Array.dispose arr in n",
        "let read := Array.get arr in let 1 changed := Array.set arr 0 7 in let n := read 0 in let _ := Array.dispose changed in n",
        "let read := Array.get arr in let 1 run:(i:Int) -> Int := fun i => Array.consume Array.sum arr in read 0 + run 0",
        "let 1 alias := arr in let read := Array.get arr in let n := read 0 in let _ := Array.dispose alias in n",
        "let 1 alias := arr in let read := Array.get alias in let n := read 0 in let _ := Array.dispose arr in n",
    ],
)
def test_owner_is_frozen_for_entire_borrowed_binding_scope(body):
    _, errors = compile_source(f"def main (_:Int):Int := let 1 arr := #[5,9] in {body};")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


@pytest.mark.parametrize(
    "definition",
    [
        "def leak (borrow f:(i:Int) -> Int):(i:Int) -> Int := f;",
        "def leak (borrow f:(i:Int) -> Int):(i:Int) -> Int := let alias := f in alias;",
        "def leak (borrow arr:(Array Int)):(i:Int) -> Int := let read:(i:Int) -> Int := fun i => Array.length arr in read;",
        "def leak (_:Int):(i:Int) -> Int := let 1 arr := #[5,9] in fun i => Array.length arr;",
    ],
)
def test_borrowed_values_cannot_escape_function_scope(definition):
    _, errors = compile_source(definition + "\ndef main (_:Int):Int := 0;")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


@pytest.mark.parametrize("quantity", ["", "1 "])
def test_borrowed_closure_requires_a_borrow_callback(quantity):
    _, errors = compile_source(f"""
def run ({quantity}f:(i:{{j:Int | j >= 0 && j < 2}}) -> Int):Int := f 0;
def main (_:Int):Int := let 1 arr := #[5,9] in
    let n := run (Array.get arr) in let _ := Array.dispose arr in n;
""")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


def test_owning_closure_cannot_be_invoked_through_borrow_callback():
    _, errors = compile_source("""
def twice (borrow f:(i:{j:Int | j >= 0 && j < 2}) -> Int):Int := f 0 + f 1;
def main (_:Int):Int := let 1 arr := #[5,9] in
    twice (fun i => Array.consume Array.sum arr);
""")
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_borrow_callback_remains_active_during_later_arguments():
    _, errors = compile_source("""
def run (borrow f:(i:{j:Int | j >= 0 && j < 2}) -> Int) (n:{j:Int | j >= 0 && j < 2}):Int := f n;
def main (_:Int):Int := let 1 arr := #[5,9] in
    run (Array.get arr) (let _ := Array.dispose arr in 0);
""")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


def test_scoped_read_in_later_argument_of_fully_applied_update():
    driver, errors = compile_source("""
def main (_:Int):Int := let 1 arr := #[5,9] in
    let 1 changed := Array.set arr (let read:(i:Int) -> {n:Int | n = Array.size arr} := fun i => Array.length arr in read 0 - 1) 7 in
    Array.consume Array.sum changed;
""")
    assert not errors, errors
    assert driver.run() == 12


def test_borrowed_factory_cannot_hide_owning_results():
    _, errors = compile_source("""
def make (_:Int):(i:Int) -> Int := let 1 arr := #[5,9] in fun i => Array.consume Array.sum arr;
def twice (borrow factory:(i:Int) -> (j:Int) -> Int):Int := let f := factory 0 in f 0 + f 1;
def main (_:Int):Int := twice make;
""")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


@pytest.mark.parametrize("callback", ["fun i => Array.length arr", "read"])
def test_borrowed_callback_cannot_alias_an_owned_argument(callback):
    binding = "let read:(i:Int) -> Int := fun i => Array.length arr in" if callback == "read" else ""
    _, errors = compile_source(f"""
def run (1 xs:(Array Int)) (borrow f:(i:Int) -> Int):Int :=
    let n := f 0 in let _ := Array.dispose xs in n;
def main (_:Int):Int := let 1 arr := #[5,9] in
    {binding} run arr ({callback});
""")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


def test_erased_borrowed_closure_is_rejected_in_terms():
    driver, errors = compile_source("""
def main (_:Int):Int := let 1 arr := #[5,9] in
    let 0 read := Array.get arr in Array.consume Array.sum arr;
""")
    from aeon.errors import ErasedBindingInTermError

    assert any(isinstance(error, ErasedBindingInTermError) for error in errors), errors


def test_partial_user_defined_borrower_keeps_dependency():
    driver, errors = compile_source("""
def read (borrow xs:(Array Int)) (a:Int) (b:Int):Int := Array.length xs + a + b;
def main (_:Int):Int := let 1 arr := #[5,9] in
    let n := (let f := read arr in let g := f 1 in g 2 + g 3) in
    let _ := Array.dispose arr in n;
""")
    assert not errors, errors
    assert driver.run() == 11


def test_borrow_scope_allows_independent_owned_result():
    driver, errors = compile_source("""
def main (_:Int):Int := let 1 arr := #[5,9] in
    let 1 copy := (let read := Array.get arr in #[read 0,read 1]) in
    let _ := Array.dispose arr in Array.consume Array.sum copy;
""")
    assert not errors, errors
    assert driver.run() == 14


def test_closure_can_own_one_resource_and_borrow_another():
    driver, errors = compile_source("""
def main (_:Int):Int := let 1 arr := #[5,9] in let 1 other := #[1,2] in
    let n := (let 1 run:(i:Int) -> Int := fun i => Array.length arr + Array.consume Array.sum other in run 0) in
    let _ := Array.dispose arr in n;
""")
    assert not errors, errors
    assert driver.run() == 5


def test_inline_borrowing_lambda_lives_through_argument_evaluation():
    _, errors = compile_source("""
def main (_:Int):Int := let 1 arr := #[5,9] in
    ((fun i => Array.length arr):(i:Int) -> Int) (let _ := Array.dispose arr in 0);
""")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


def test_partial_borrow_cannot_retain_an_anonymous_owner():
    _, errors = compile_source("""
def main (_:Int):Int := let read := Array.get #[5,9] in read 0 + read 1;
""")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


def test_borrow_callback_can_forward_a_curried_borrow():
    driver, errors = compile_source("""
def run (borrow f:(i:Int) -> Int):Int := f 0 + f 1;
def forward (borrow f:(a:Int) -> (b:Int) -> Int):Int := let g := f 2 in run g;
def read (borrow xs:(Array Int)) (a:Int) (b:Int):Int := Array.length xs + a + b;
def main (_:Int):Int := let 1 arr := #[5,9] in
    let n := forward (read arr) in let _ := Array.dispose arr in n;
""")
    assert not errors, errors
    assert driver.run() == 9


@pytest.mark.parametrize("quantity", ["1 ", ""])
def test_borrowed_closure_cannot_be_hidden_by_polymorphic_storage(quantity):
    _, errors = compile_source(f"""
type Box
def pack : forall a:*, ({quantity}value:a) -> Box := Λa:* => fun value => native "value";
def main (_:Int):Int := let 1 arr := #[5,9] in
    let box := pack (Array.get arr) in let _ := Array.dispose arr in 0;
""")
    assert any(isinstance(error, BorrowingError) for error in errors), errors


def test_imported_borrow_callback_with_cached_module(tmp_path, monkeypatch):
    from aeon.compilation.compile import clear_unit_cache, compile_file

    monkeypatch.chdir(tmp_path)
    library = tmp_path / "Scoped.ae"
    library.write_text("def run (borrow f:(i:Int) -> Int):Int := f 0 + f 1;")
    _, errors = compile_file(str(library), is_main=False, write_cache=True)
    assert not errors, errors
    clear_unit_cache()
    driver, errors = compile_source("""
import Scoped;
def main (_:Int):Int := let 1 arr := #[5,9] in
    let n := Scoped.run (fun i => Array.length arr + i) in
    let _ := Array.dispose arr in n;
""")
    assert not errors, errors
    assert driver.run() == 5
