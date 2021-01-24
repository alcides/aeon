from aeon.typing.context import EmptyContext
from aeon.synthesis.synthesis import syntht
from aeon.synthesis.sources import SeededRandomSource
from aeon.frontend.parser import parse_type, parse_term

seed = lambda x: SeededRandomSource(x)


def test_source():
    r = SeededRandomSource(seed=1)
    assert r.next_integer() == 17611
    assert r.next_integer() == 74606
    assert r.choose([1, 2, 3, 4]) == 4


def test_synthesis():
    assert syntht(seed(1234), EmptyContext,
                  parse_type("Int")) == parse_term("15535")
