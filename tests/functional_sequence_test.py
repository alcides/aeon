"""Persistent sequence operations shared by functional synthesis benchmarks."""

import pytest

from aeon.bindings.lists import from_iterable, to_list
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

setup_logger()


@pytest.mark.parametrize(
    "expression,ty,expected",
    [
        ("List.foldl (fun total => fun x => total * 10 + x) 0 [1, 2, 3]", "Int", 123),
        ("List.filter (fun x => x % 2 = 0) [3, 2, 4, 2]", "(List Int)", [2, 4, 2]),
        ("List.zipWith (fun x => fun y => x - y) [1, 2, 3] [4, 5]", "(List Int)", [-3, -3]),
        ("List.zipWith (fun x => fun y => x + y) [] [4, 5]", "(List Int)", []),
        ("List.take 2 [1, 2, 3]", "(List Int)", [1, 2]),
        ("List.take 5 [1, 2]", "(List Int)", [1, 2]),
        ("List.take (-1) [1, 2]", "(List Int)", []),
        ("List.drop 2 [1, 2, 3]", "(List Int)", [3]),
        ("List.drop 5 [1, 2]", "(List Int)", []),
        ("List.drop (-1) [1, 2]", "(List Int)", [1, 2]),
        ("List.range (-2) 2", "(List Int)", [-2, -1, 0, 1]),
        ("List.range 3 1", "(List Int)", []),
        ("List.sumFloat [1.5, (-0.25), 2.0]", "Float", 3.25),
        ("List.removeFirst 2 [1, 2, 3, 2]", "(List Int)", [1, 3, 2]),
        ("List.removeFirst 4 [1, 2, 3]", "(List Int)", [1, 2, 3]),
        ('String.characters "a🙂ß"', "(List String)", ["a", "🙂", "ß"]),
        ('String.splitList "a,,b," ","', "(List String)", ["a", "", "b", ""]),
        ('String.splitList "" ","', "(List String)", [""]),
        ('String.joinList "::" ["a", "", "b"]', "String", "a::::b"),
        ('String.reverse "a🙂ß"', "String", "ß🙂a"),
        ('String.capitalize "hELLO WORLD"', "String", "Hello world"),
    ],
)
def test_functional_sequence_operations(expression, ty, expected):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=False))
    assert not driver.parse(aeon_code=f"import List; import String; def main (_:Int) : {ty} := {expression};")
    actual = driver.run()
    assert (to_list(actual) if isinstance(expected, list) else actual) == expected


def test_list_boundary_checks_representation_and_preserves_elements():
    values = [1, "x", from_iterable([2, 3])]
    assert to_list(from_iterable(iter(values))) == values
    with pytest.raises(ValueError, match="Aeon List"):
        to_list(("List_cons", 1, [2]))


def test_split_list_rejects_an_empty_separator():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    assert driver.parse(aeon_code='import String; def bad : (List String) := String.splitList "abc" "";')
