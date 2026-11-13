"""Owning closures carry QTT obligations across storage and higher-order calls."""

import pytest

from aeon.errors import LinearityError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_source(source, *, contracts=False):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, contracts=contracts))
    errors = list(driver.parse(aeon_code="import Array;\n" + source))
    return driver, errors


@pytest.mark.parametrize("contracts", [False, True])
@pytest.mark.parametrize(
    "body,expected",
    [
        ("let 1 update := Array.set arr in Array.consume Array.sum (update 0 7)", 16),
        ("let 1 update := Array.set arr 0 in Array.consume Array.sum (update 7)", 16),
        ("let 1 f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in f 0", 14),
        ("let 1 f:(x:Int) -> Int := fun x => let n := Array.length arr in n + Array.consume Array.sum arr in f 0", 16),
        ("let 1 f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in let 1 g := f in g 0", 14),
        (
            "let 1 f:(x:Int) -> (y:Int) -> Int := fun x => fun y => Array.consume Array.sum arr in let 1 g := f 0 in g 1",
            14,
        ),
        (
            "let 1 f:(x:Int) -> Int := if true then fun x => Array.consume Array.sum arr else fun x => Array.consume Array.sum arr in f 0",
            14,
        ),
        ("let 1 f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in if true then f 0 else f 1", 14),
    ],
)
def test_owning_closure_runs_once(body, expected, contracts):
    driver, errors = compile_source(f"def main (_:Int):Int := let 1 arr := #[5,9] in {body};", contracts=contracts)
    assert not errors, errors
    assert driver.run() == expected


@pytest.mark.parametrize(
    "body",
    [
        "let f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in f 0",
        "let 1 f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in 0",
        "let 1 f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in f 0 + f 1",
        "let 1 f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in let g := f in g 0 + g 1",
        "let 1 f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in if true then f 0 else 0",
        "let 1 f:(x:Int) -> Int := fun x => Array.consume Array.sum arr in Array.length arr + f 0",
        "let 1 update := Array.set arr in Array.consume Array.sum (update (Array.length arr - 1) 7)",
        "let 1 f:(x:Int) -> Int := fun x => Array.length arr in let n := f 0 in n + Array.consume Array.sum arr",
        "let 1 get := Array.get arr in let n := get 0 in n + Array.consume Array.sum arr",
        "let 1 f:(x:Int) -> Int := fun x => let n := Array.consume Array.sum arr in n + Array.length arr in f 0",
        "let 1 f:(x:Int) -> Int := fun x => if x > 0 then f (x - 1) else Array.consume Array.sum arr in f 1",
    ],
)
def test_ownership_cannot_be_duplicated_dropped_or_borrowed_after_capture(body):
    _, errors = compile_source(f"def main (_:Int):Int := let 1 arr := #[5,9] in {body};")
    assert any(isinstance(error, LinearityError) for error in errors), errors


FACTORY = """
def make (_:Int):(x:Int) -> Int :=
    let 1 arr := #[5,9] in fun x => Array.consume Array.sum arr;
"""


def test_factory_returns_an_owning_closure():
    driver, errors = compile_source(FACTORY + "def main (_:Int):Int := let 1 f := make 0 in f 0;")
    assert not errors, errors
    assert driver.run() == 14


@pytest.mark.parametrize("body", ["let f := make 0 in f 0 + f 1", "let f := make 0 in 0"])
def test_factory_result_cannot_lose_ownership(body):
    _, errors = compile_source(FACTORY + f"def main (_:Int):Int := {body};")
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_linear_higher_order_factory():
    driver, errors = compile_source(
        FACTORY
        + """
def run (1 maker:(x:Int) -> (y:Int) -> Int):Int := let 1 f := maker 0 in f 0;
def main (_:Int):Int := run make;
"""
    )
    assert not errors, errors
    assert driver.run() == 14


def test_unrestricted_higher_order_signature_cannot_hide_owned_results():
    _, errors = compile_source(
        FACTORY
        + """
def run (maker:(x:Int) -> (y:Int) -> Int):Int := let f := maker 0 in f 0 + f 1;
def main (_:Int):Int := run make;
"""
    )
    assert any(isinstance(error, LinearityError) for error in errors), errors


@pytest.mark.parametrize("quantity", ["1 ", ""])
def test_polymorphic_identity_preserves_closure_ownership(quantity):
    driver, errors = compile_source(
        FACTORY
        + f"""
def keep : forall a:*, (1 value:a) -> a := Λa:* => fun value => value;
def main (_:Int):Int := let {quantity}f := keep (make 0) in f 0;
"""
    )
    if quantity:
        assert not errors, errors
        assert driver.run() == 14
    else:
        assert any(isinstance(error, LinearityError) for error in errors), errors


def test_scalar_capture_and_ordinary_partial_application_remain_reusable():
    driver, errors = compile_source("""
def add (x:Int) (y:Int):Int := x + y;
def main (_:Int):Int := let f := add 3 in f 1 + f 2;
""")
    assert not errors, errors
    assert driver.run() == 9


def test_builtin_scalar_partial_application_remains_reusable():
    driver, errors = compile_source("""
def main (_:Int):Int := let f := (+) 3 in f 1 + f 2;
""")
    assert not errors, errors
    assert driver.run() == 9


def test_closure_capturing_a_linear_scalar_is_linear():
    driver, errors = compile_source("""
def take (1 x:Int):Int := x;
def main (_:Int):Int := let 1 x := 7 in let 1 f:(u:Int) -> Int := fun u => take x in f 0;
""")
    assert not errors, errors
    assert driver.run() == 7


@pytest.mark.parametrize("erased", ["let 0 ghost:(u:Int) -> Int := fun u => Array.consume Array.sum arr in", ""])
def test_erased_closure_does_not_capture_runtime_ownership(erased):
    driver, errors = compile_source(f"""
def ignore (0 f:(u:Int) -> Int):Int := 0;
def main (_:Int):Int := let 1 arr := #[5,9] in {erased}
    ignore (fun u => Array.consume Array.sum arr) + Array.consume Array.sum arr;
""")
    assert not errors, errors
    assert driver.run() == 14


def test_linear_argument_does_not_make_scalar_results_owning():
    driver, errors = compile_source("""
def keep : forall a:*, (1 value:a) -> a := Λa:* => fun value => value;
def take (1 value:Int):Int := value;
def run (f:(1 value:Int) -> Int):Int := f 7;
def main (_:Int):Int := run take + run (keep{Int});
""")
    assert not errors, errors
    assert driver.run() == 14


@pytest.mark.parametrize("quantity", ["1 ", ""])
def test_container_retains_closure_ownership(quantity):
    driver, errors = compile_source(
        FACTORY
        + f"""
type Box
def pack (1 f:(x:Int) -> Int):Box := native "f";
def unpack (1 box:Box):(x:Int) -> Int := fun x => native "box(x)";
def main (_:Int):Int := let {quantity}box := pack (make 0) in let 1 f := unpack box in f 0;
"""
    )
    if quantity:
        assert not errors, errors
        assert driver.run() == 14
    else:
        assert any(isinstance(error, LinearityError) for error in errors), errors


def test_higher_order_factory_cannot_be_hidden_in_a_polymorphic_box():
    _, errors = compile_source(
        FACTORY
        + """
type Box
def pack : forall a:*, (1 value:a) -> Box := Λa:* => fun value => native "value";
def unpack (1 box:Box):(x:Int) -> (y:Int) -> Int := fun x => fun y => native "box(x)(y)";
def main (_:Int):Int :=
    let box := pack make in
    let factory := unpack box in
    let f := factory 0 in f 0 + f 1;
"""
    )
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_returned_closure_keeps_its_obligation_through_an_annotation():
    _, errors = compile_source(
        FACTORY
        + """
def main (_:Int):Int := let f:(x:Int) -> Int := make 0 in f 0 + f 1;
"""
    )
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_recursive_factory_cannot_duplicate_its_recursive_result():
    _, errors = compile_source("""
def make (n:Int):(x:Int) -> Int :=
    if n > 0 then
        let f := make (n - 1) in fun x => f 0 + f 1
    else
        let 1 arr := #[5,9] in fun x => Array.consume Array.sum arr;
def main (_:Int):Int := let 1 f := make 1 in f 0;
""")
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_recursive_opaque_result_analysis_converges():
    from aeon.core.terms import Abstraction, Literal, Rec, Var
    from aeon.core.types import AbstractionType, Top, t_int
    from aeon.typechecking.linearity import check_linearity
    from aeon.utils.name import Name

    name, parameter = Name("self", 1), Name("x", 2)
    term = Rec(name, AbstractionType(parameter, t_int, Top()), Abstraction(parameter, Var(name)), Literal(0, t_int))
    assert check_linearity(term) == []


def test_recursive_list_results_remain_reusable():
    driver, errors = compile_source("""
import List;
def main (_:Int):Int :=
    let values := List.append [1,2] [3] in List.length values + List.length values;
""")
    assert not errors, errors
    assert driver.run() == 6


@pytest.mark.parametrize("quantity", ["1 ", ""])
def test_mutually_recursive_factories_preserve_owned_results(quantity):
    driver, errors = compile_source(f"""
mutual
    def first (n:Int):(i:Int) -> Int := second n;
    def second (n:Int):(i:Int) -> Int :=
        if n > 0 then first (n - 1) else
        let 1 arr := #[5,9] in fun i => Array.consume Array.sum arr;
end
def main (_:Int):Int := let {quantity}f := first 1 in f 0;
""")
    if quantity:
        assert not errors, errors
        assert driver.run() == 14
    else:
        assert any(isinstance(error, LinearityError) for error in errors), errors


@pytest.mark.parametrize("quantity", ["1 ", ""])
def test_imported_factory_preserves_ownership_with_cached_modules(tmp_path, monkeypatch, quantity):
    from aeon.compilation.compile import clear_unit_cache, compile_file

    monkeypatch.chdir(tmp_path)
    library = tmp_path / "Factory.ae"
    library.write_text("import Array;\n" + FACTORY)
    _, errors = compile_file(str(library), is_main=False, write_cache=True)
    assert not errors, errors
    clear_unit_cache()
    driver, errors = compile_source(f"""
import Factory;
def main (_:Int):Int := let {quantity}f := Factory.make 0 in f 0;
""")
    if quantity:
        assert not errors, errors
        assert driver.run() == 14
    else:
        assert any(isinstance(error, LinearityError) for error in errors), errors


def test_owning_closures_example():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(driver.parse(filename="examples/syntax/owning_closures.ae"))
    assert not errors, errors
    assert driver.run() == 27
