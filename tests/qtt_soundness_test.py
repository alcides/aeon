"""Function quantities remain enforceable through subtyping and term wrappers."""

import pytest

from aeon.core.multiplicity import M0, M1, MN, MOmega, MBorrow, usage_subtype
from aeon.core.terms import Abstraction, Literal
from aeon.core.types import AbstractionType, t_int
from aeon.errors import ErasedBindingInTermError, LinearUnusedError, ErasedUsedAtRuntimeError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.name import Name


def compile_source(source):
    driver = AeonDriver(AeonConfig("tdsyn", SilentSynthesisUI(), 1))
    return driver, list(driver.parse(aeon_code=source))


@pytest.mark.parametrize("actual", [M0, M1, MN, MOmega, MBorrow])
@pytest.mark.parametrize("expected", [M0, M1, MN, MOmega, MBorrow])
def test_quantity_subtyping(actual, expected):
    allowed = {
        M0: {M0, MOmega},
        M1: {M1, MOmega},
        MN: {M0, M1, MN, MOmega},
        MOmega: {MOmega},
        MBorrow: {MBorrow},
    }
    assert usage_subtype(actual, expected) == (expected in allowed[actual])


@pytest.mark.parametrize(
    "parameter,body,target",
    [
        ("x:Int", "x + x", "1 x:Int"),
        ("0 x:Int", "0", "1 x:Int"),
        ("x:Int", "x", "0 x:Int"),
        ("1 x:Int", "x", "0 x:Int"),
    ],
)
def test_function_alias_cannot_strengthen_usage_guarantee(parameter, body, target):
    _, errors = compile_source(f"""
        def original ({parameter}):Int := {body};
        def disguised : ({target}) -> Int := original;
        def main (u:Int):Int := disguised 7;
    """)
    assert errors


@pytest.mark.parametrize("parameter,body", [("1 x:Int", "x"), ("0 x:Int", "0")])
def test_function_alias_can_weaken_guarantee_to_unrestricted(parameter, body):
    driver, errors = compile_source(f"""
        def original ({parameter}):Int := {body};
        def reusable : (x:Int) -> Int := original;
        def main (u:Int):Int := reusable 7;
    """)
    assert not errors, errors
    assert isinstance(driver.run(), int)


@pytest.mark.parametrize(
    "parameter,body,error",
    [
        ("1 x:Int", "0", LinearUnusedError),
        ("0 x:Int", "x", ErasedUsedAtRuntimeError),
    ],
)
def test_let_continuation_preserves_expected_function_quantity(parameter, body, error):
    _, errors = compile_source(f"""
        def bad : ({parameter}) -> Int := let z := 0 in (fun x => {body});
        def main (u:Int):Int := bad 7;
    """)
    assert any(isinstance(e, error) for e in errors), errors


def test_typecheck_errors_checks_root_function_signature():
    x = Name("x", 1)
    errors = list(
        check_type_errors(
            TypingContext(), Abstraction(x, Literal(0, t_int)), AbstractionType(x, t_int, t_int, multiplicity=M1)
        )
    )
    assert any(isinstance(e, LinearUnusedError) for e in errors), errors


@pytest.mark.parametrize("binding", ["let 0 ghost := 5", "let 0 ghost:Int := 5", 'let 0 ghost:Int := native "0"'])
def test_erased_term_binding_is_forbidden(binding):
    _, errors = compile_source(f"def main (u:Int):Int := {binding} in 42;")
    assert any(isinstance(e, ErasedBindingInTermError) for e in errors), errors


def test_erased_predicate_binding_remains_allowed():
    driver, errors = compile_source("""
        def keep (x:Int):{v:Int | let 0 expected := x in v = expected} := x;
        def main (u:Int):Int := keep 7;
    """)
    assert not errors, errors
    assert driver.run() == 7


def test_higher_order_callback_cannot_hide_unrestricted_usage():
    _, errors = compile_source("""
        def dup (x:Int):Int := x + x;
        def invoke (f:(1 x:Int) -> Int) (1 value:Int):Int := f value;
        def main (u:Int):Int := invoke dup 7;
    """)
    assert errors


def test_typed_let_continuation_preserves_expected_function_quantity():
    _, errors = compile_source("""
        def bad : (1 x:Int) -> Int := let z:Int := 0 in (fun x => 0);
        def main (u:Int):Int := bad 7;
    """)
    assert any(isinstance(e, LinearUnusedError) for e in errors), errors
