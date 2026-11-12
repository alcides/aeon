"""Array constructors preserve contents, size refinements, and ownership."""

import pytest

from aeon.facade.api import LinearityError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_source(source):
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0))
    errors = list(driver.parse(aeon_code="open Array;\n" + source))
    return driver, errors


def assert_array(expression, values):
    source = f"""
def matches (1 xs:(Array Int)) : Bool := native "xs == {values}";
def main (_:Int) : Bool :=
    let 1 xs : {{r:(Array Int) | size r = {len(values)}}} := {expression} in
    matches xs;
"""
    driver, errors = compile_source(source)
    assert not errors, errors
    assert driver.run() is True


@pytest.mark.parametrize("arity", [1, 2, 4, 8, 16, 32])
def test_fixed_arity_contents_and_size(arity):
    values = list(range(arity))
    assert_array(f"mk_{arity} " + " ".join(map(str, values)), values)


@pytest.mark.parametrize("size", [0, 1, 3, 31, 32, 33, 63, 64, 65, 100])
def test_literal_arbitrary_lengths(size):
    values = list(range(size))
    assert_array("#[" + ", ".join(map(str, values)) + "]", values)


@pytest.mark.parametrize("size", [0, 1, 37])
def test_repeat_contents_size_and_element_refinement(size):
    assert_array(f"mk_repeat {size} 7", [7] * size)
    _, errors = compile_source(f"""
def needs_sevens (1 xs:{{r:(Array {{v:Int | v = 7}}) | size r = {size}}}) : Int := (Array.consume Array.sum) xs;
def main (_:Int) : Int := needs_sevens (mk_repeat {size} 7);
""")
    assert not errors, errors


@pytest.mark.parametrize(
    "expression,values",
    [
        ("mk_concat (mk_2 1 2) (mk_4 3 4 5 6)", [1, 2, 3, 4, 5, 6]),
        ("mk_concat (mk_empty unit) (mk_2 1 2)", [1, 2]),
        ("mk_concat (mk_2 1 2) (mk_empty unit)", [1, 2]),
        ("mk_concat (mk_empty unit) (mk_empty unit)", []),
    ],
)
def test_concat_order_and_size(expression, values):
    assert_array(expression, values)


@pytest.mark.parametrize("value,accepted", [(3, True), (0, False)])
def test_concat_preserves_and_enforces_element_refinement(value, accepted):
    _, errors = compile_source(f"""
def positive (1 xs:(Array {{v:Int | v > 0}})) : Int := (Array.consume Array.sum) xs;
def main (_:Int) : Int := positive (mk_concat (mk_2 1 2) (mk_1 {value}));
""")
    assert (not errors) == accepted, errors


@pytest.mark.parametrize("expression", ["mk_repeat (-1) 7", "Array.get (mk_2 1 2) 2"])
def test_invalid_sizes_and_indices_are_rejected(expression):
    _, errors = compile_source(
        f"def main (_:Int) : Int := {'length (' + expression + ')' if expression.startswith('mk_repeat') else expression};"
    )
    assert errors
    assert not any(isinstance(error, LinearityError) for error in errors)


@pytest.mark.parametrize("expression", ["mk_concat xs xs", "mk_repeat 2 xs"])
def test_constructors_cannot_duplicate_linear_arrays(expression):
    _, errors = compile_source(f"""
def main (_:Int) : Int :=
    let 1 xs := mk_2 1 2 in
    length ({expression});
""")
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_repeat_cannot_duplicate_an_inline_linear_array():
    _, errors = compile_source("def main (_:Int) : Int := length (mk_repeat 2 (mk_2 1 2));")
    assert any(isinstance(error, LinearityError) for error in errors), errors


@pytest.mark.parametrize("expression", ["mk_empty unit", "mk_concat (mk_empty unit) (mk_1 1)"])
def test_empty_arrays_admit_element_refinements(expression):
    _, errors = compile_source(f"""
def positive (1 xs:(Array {{v:Int | v > 0}})) : Int := (Array.consume Array.sum) xs;
def main (_:Int) : Int := positive ({expression});
""")
    assert not errors, errors


@pytest.mark.parametrize("expression", ["mk_empty unit", "mk_repeat 3 7"])
def test_each_constructor_call_allocates_fresh_storage(expression):
    driver, errors = compile_source(f"""
def independent (1 xs:(Array Int)) (1 ys:(Array Int)) : Bool := native "xs is not ys and xs == ys";
def make (_:Unit) : (Array Int) := {expression};
def main (_:Int) : Bool := independent (make unit) (make unit);
""")
    assert not errors, errors
    assert driver.run() is True


def test_nested_literal_moves_each_array_once():
    driver, errors = compile_source("""
def flatten (1 xs:(Array (Array Int))) : (Array Int) := native "[x for row in xs for x in row]";
def main (_:Int) : Int :=
    let 1 a := mk_2 1 2 in
    let 1 b := mk_1 3 in
    (Array.consume Array.sum) (flatten #[a, b]);
""")
    assert not errors, errors
    assert driver.run() == 6


@pytest.mark.parametrize("value,accepted", [(3, True), (0, False)])
def test_nested_literals_preserve_element_refinements(value, accepted):
    _, errors = compile_source(f"""
def positive (1 xs:(Array (Array {{v:Int | v > 0}}))) : Int :=
    native "sum(sum(row) for row in xs)";
def main (_:Int) : Int := positive #[#[1, 2], #[{value}]];
""")
    assert (not errors) == accepted, errors


def test_nested_literals_reject_mixed_element_types():
    _, errors = compile_source("def main (_:Int) : Int := length #[#[1], #[true]];")
    assert errors


def test_literal_evaluates_elements_once_in_order_across_chunks():
    values = list(range(35))
    literal = "#[" + ", ".join(f"record trace {n}" for n in values) + "]"
    driver, errors = compile_source(f"""
type Trace
def new_trace (_:Unit) : Trace := native "[]";
def record (trace:Trace) (n:Int) : Int := native "(trace.append(n), n)[1]";
def matches (trace:Trace) (1 xs:(Array Int)) : Bool := native "trace == xs == {values}";
def main (_:Int) : Bool :=
    let trace := new_trace unit in
    let 1 xs := {literal} in
    matches trace xs;
""")
    assert not errors, errors
    assert driver.run() is True
