"""Array reads in refinements agree with their literal runtime contents."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _parse(source):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = driver.parse(aeon_code="import Array;\n" + source)
    return driver, errors


@pytest.mark.parametrize(
    "element,contents,expected,value",
    [
        ("Int", "9, 11, 15", "11", 11),
        ("Float", "1.5, 2.5, 3.5", "2.5", 2.5),
        ("Bool", "false, true, false", "true", True),
        ("String", '"a", "b", "c"', '"b"', "b"),
    ],
)
def test_literal_read_proves_exact_element(element, contents, expected, value):
    driver, errors = _parse(f"""
        def table (_:Unit): {{a:(Array {element}) | Array.size a = 3}} := #[{contents}];
        def main (_:Int): {{v:{element} | v = {expected}}} := Array.get (table unit) 1;
    """)
    assert not errors, errors
    assert driver.run() == value


@pytest.mark.parametrize("expected,valid", [(11, True), (9, False)])
def test_symbolic_index_preserves_element_order(expected, valid):
    _, errors = _parse(f"""
        def read (i:{{n:Int | n = 1}}): {{v:Int | v = {expected}}} := Array.take #[9, 11, 15] i;
        def main (_:Int):Int := read 1;
    """)
    assert (not errors) == valid


def test_read_across_literal_chunk_boundary():
    values = ", ".join(str(i * 3) for i in range(50))
    driver, errors = _parse(f"""
        def table (_:Unit): {{a:(Array Int) | Array.size a = 50}} := #[{values}];
        def main (_:Int): {{v:Int | v = 147}} := Array.get (table unit) 49;
    """)
    assert not errors, errors
    assert driver.run() == 147


@pytest.mark.parametrize("index", [-1, 3])
def test_out_of_bounds_read_is_rejected(index):
    _, errors = _parse(f"def main (_:Int):Int := Array.take #[9, 11, 15] ({index});")
    assert errors


def test_user_function_cannot_impersonate_an_internal_array_operation():
    _, errors = _parse("""
        def __array_get (1 arr:(Array Int)) (i:Int):Int := native "0";
        def main (_:Int): {v:Int | v = 11} := __array_get #[9, 11, 15] 1;
    """)
    assert errors
