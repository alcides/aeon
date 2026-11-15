"""Array contracts enforce callback domains and preserve values and lengths."""

import pytest

from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _compile(source):
    driver = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 0))
    errors = list(driver.parse(aeon_code="open Array;\n" + source))
    return driver, errors


@pytest.mark.parametrize(
    "signature, body, expression, expected",
    [
        ("(x:{v:Int | v > 0}):Int", "10 / x", "sum (map callback (mk_1 VALUE))", 5),
        ("(x:{v:Int | v > 0}):Bool", "10 / x > 0", "length (filter callback (mk_1 VALUE))", 1),
        ("(x:{v:Int | v > 0}) (acc:Int):Int", "acc + 10 / x", "reduce callback 0 (mk_1 VALUE)", 5),
        ("(x:{v:Int | v > 0}):Bool", "10 / x > 0", "count callback (mk_1 VALUE)", 1),
        (
            "(i:{n:Int | 0 <= n && n < 1}) (x:{v:Int | v > 0}):Int",
            "10 / x + i",
            "sum (imap (mk_1 VALUE) callback)",
            5,
        ),
        (
            "(x:{v:Int | v > 0}) (y:{v:Int | v > 0}):Int",
            "10 / x + 10 / y",
            "sum (zipWith callback (mk_1 VALUE) (mk_1 2))",
            10,
        ),
        (
            "(x:{v:Int | v > 0}) (y:{v:Int | v > 0}):Int",
            "10 / x + 10 / y",
            "sum (zipWith callback (mk_1 2) (mk_1 VALUE))",
            10,
        ),
    ],
    ids=["map", "filter", "reduce", "count", "imap", "zip_left", "zip_right"],
)
@pytest.mark.parametrize("value", [2, 0], ids=["valid", "invalid"])
def test_callback_preconditions(signature, body, expression, expected, value):
    expression = expression.replace("VALUE", str(value))
    driver, errors = _compile(f"def callback {signature} := {body};\ndef main (_:Int):Int := {expression};")
    if value == 0:
        assert any(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors), errors
    else:
        assert not errors, errors
        assert driver.run() == expected


@pytest.mark.parametrize(
    "expression, size_predicate, expected",
    [
        ("set (mk_repeat 2 7) 0 8", "size r = 2", 15),
        ("reversed (mk_repeat 2 7)", "size r = 2", 14),
        ("filter (fun x => true) (mk_repeat 2 7)", "0 <= size r && size r <= 2", 14),
        ("map (fun x => 7) (mk_repeat 2 0)", "size r = 2", 14),
        ("imap (mk_repeat 2 0) (fun i => fun x => i + 1)", "size r = 2", 3),
        ("zipWith (fun x => fun y => 7) (mk_repeat 2 0) (mk_repeat 2 0)", "size r = 2", 14),
    ],
    ids=["set", "reversed", "filter", "map", "imap", "zipWith"],
)
def test_element_and_length_guarantees(expression, size_predicate, expected):
    driver, errors = _compile(f"""
def positive_sum (1 xs:{{r:(Array {{v:Int | v > 0}}) | {size_predicate}}}):Int := (consume sum) xs;
def main (_:Int):Int := positive_sum ({expression});
""")
    assert not errors, errors
    assert driver.run() == expected


@pytest.mark.parametrize("positive", [True, False])
def test_get_uses_the_input_element_predicate(positive):
    predicate = "n > 0" if positive else "n < 0"
    driver, errors = _compile(f"def main (_:Int):{{n:Int | {predicate}}} := get (mk_repeat 2 7) 0;")
    if positive:
        assert not errors, errors
        assert driver.run() == 7
    else:
        assert any(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors), errors


@pytest.mark.parametrize(
    "expression",
    [
        "set (mk_repeat 2 7) 0 0",
        "reversed (mk_1 0)",
        "filter (fun x => true) (mk_1 0)",
        "map (fun x => 0) (mk_1 7)",
        "imap (mk_1 7) (fun i => fun x => 0)",
        "zipWith (fun x => fun y => 0) (mk_1 7) (mk_1 7)",
    ],
)
def test_transforms_cannot_invent_positive_elements(expression):
    _, errors = _compile(f"""
def positive_sum (1 xs:(Array {{v:Int | v > 0}})):Int := (consume sum) xs;
def main (_:Int):Int := positive_sum ({expression});
""")
    assert any(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors), errors


@pytest.mark.parametrize("index_refinement, accepted", [("0 <= n && n < 3", True), ("n > 0", False), ("n < 2", False)])
def test_imap_bounds_both_ends_of_the_index(index_refinement, accepted):
    driver, errors = _compile(f"""
def index_value (i:{{n:Int | {index_refinement}}}) (x:Int):Int := i;
def main (_:Int):Int := sum (imap (mk_repeat 3 7) index_value);
""")
    if accepted:
        assert not errors, errors
        assert driver.run() == 3
    else:
        assert any(isinstance(error, LiquidTypeCheckingFailedRelation) for error in errors), errors


def test_imap_index_bound_depends_on_the_input_length():
    driver, errors = _compile("""
def indexed (n:{n:Int | n >= 0}) (1 xs:{r:(Array Int) | size r = n}):
    {r:(Array Int) | size r = n} :=
    let index_value : (i:{i:Int | 0 <= i && i < n}) -> (x:Int) -> Int := fun i => fun x => i in
    imap xs index_value;
def main (_:Int):Int := sum (indexed 3 (mk_repeat 3 7));
""")
    assert not errors, errors
    assert driver.run() == 3


@pytest.mark.parametrize(
    "expression",
    ["(consume length) xs", "(consume length) (filter (fun x => true) xs)"],
)
def test_lengths_of_arbitrary_arrays_are_nonnegative(expression):
    driver, errors = _compile(f"""
def nonnegative (1 xs:(Array Int)):{{n:Int | n >= 0}} := {expression};
def main (_:Int):Int := nonnegative (mk_empty unit);
""")
    assert not errors, errors
    assert driver.run() == 0


def test_filter_length_bounds_hold_for_arbitrary_arrays():
    driver, errors = _compile("""
def keep_positive (1 xs:(Array Int)):
    {ys:(Array Int) | 0 <= size ys && size ys <= size xs} := filter (fun x => x > 0) xs;
def main (_:Int):Int := length (keep_positive (mk_2 (-1) 7));
""")
    assert not errors, errors
    assert driver.run() == 1


@pytest.mark.parametrize(
    "expression",
    [
        "length (map (fun x => 10 / x) (mk_empty unit))",
        "length (imap (mk_empty{Int} unit) (fun i => fun x => i))",
        "reduce (fun x => fun acc => x + acc) 7 (mk_empty unit)",
    ],
)
def test_empty_arrays_remain_valid_for_total_collection_operations(expression):
    driver, errors = _compile(f"def main (_:Int):Int := {expression};")
    assert not errors, errors
    assert driver.run() == (7 if expression.startswith("reduce") else 0)
