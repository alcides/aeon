from aeon.typing.context import EmptyContext
from aeon.synthesis.synthesis import syntht
from aeon.synthesis.sources import ListRandomSource, SeededRandomSource
from aeon.frontend.parser import parse_type, parse_term

seed = lambda x: SeededRandomSource(x)
list = lambda x: ListRandomSource(x)


def test_seed_source():
    r = SeededRandomSource(seed=12)
    assert r.next_integer() == 24405
    assert r.choose([1, 2, 3, 4]) == 4


def test_list_source():
    l = ListRandomSource([1, 2, 3])
    assert l.next_integer() == 1
    assert l.next_integer() == 2
    assert l.next_integer() == 3
    assert l.choose([1, 2, 3]) == 2


def test_synthesis():
    assert syntht(list([0]), EmptyContext,
                  parse_type("Int")) == parse_term("0")
