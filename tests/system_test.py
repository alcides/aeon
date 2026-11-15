"""System measurements report Python runtime storage, not collection length."""

import sys

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def size_of(expression: str) -> int:
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=False))
    source = f"import System; import List; def main (_:Int) : Int := System.getSizeOf {expression};"
    assert not driver.parse(aeon_code=source)
    return driver.run()


@pytest.mark.parametrize(
    "expression, value",
    [
        ("42", 42),
        ('"hello"', "hello"),
        ("([] : (List Int))", ("List_nil",)),
        ("[1]", ("List_cons", 1, ("List_nil",))),
    ],
)
def test_get_size_of_matches_python_runtime(expression, value):
    assert size_of(expression) == sys.getsizeof(value)


def test_get_size_of_is_bytes_not_number_of_elements():
    # Each string has one character, but their Python storage differs.
    ascii_size, unicode_size = size_of('"a"'), size_of('"\u20ac"')
    assert ascii_size == sys.getsizeof("a")
    assert unicode_size == sys.getsizeof("\u20ac")
    assert ascii_size != unicode_size
    assert ascii_size > 1 and unicode_size > 1


def test_get_size_of_excludes_referenced_list_tail():
    # A cons cell always stores its tag, head and tail reference. The tail's
    # cells are separate objects and are not part of the shallow byte count.
    assert size_of("[1]") == size_of("[1, 2, 3]")
