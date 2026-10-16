from pathlib import Path

import pytest

from aeon.benchmarks.inventory import term_hole_names


@pytest.mark.parametrize(
    "source, expected",
    [
        ("def f(x:Int):{v:Int | ?p} := x;", ()),
        ("def f(x:Int):{v:Int | ?p} := ?h;", ("h",)),
        ("def f(x:Int):Int := if ?cond then ?value else ?value;", ("cond", "value")),
        ('# ?comment\ndef s:String := "?literal"; # ?other\n', ()),
        ("def f : (x:{v:Int | ?input_pred}) -> {r:Int | ?output_pred} := ?implementation;", ("implementation",)),
    ],
)
def test_only_expression_holes_are_scheduled(source, expected):
    assert term_hole_names(source) == expected


def test_inference_companion_has_no_term_holes():
    path = Path(__file__).resolve().parents[1] / "examples/liquidhaskell/positive/inferred_absolute.ae"
    assert term_hole_names(path.read_text(), str(path)) == ()


def test_malformed_source_is_not_silently_labeled_hole_free():
    with pytest.raises(Exception):
        term_hole_names("def f(x:Int):Int := if ?h then ;")
