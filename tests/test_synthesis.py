import random
from typing import Dict
from aeon.typing.context import EmptyContext, TypingContext, VariableBinder
from aeon.synthesis.synthesis import synth_term
from aeon.synthesis.sources import ListRandomSource, SeededRandomSource
from aeon.frontend.parser import parse_type, parse_term

seed = lambda x: SeededRandomSource(x)
listr = lambda x: ListRandomSource(x)

rseed = [random.randint(-100000, 100000) for _ in range(10000)]

empty = EmptyContext()


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


def helper_syn(l, ty: str, term: str, dctx: Dict[str, str] = None):
    ctx: TypingContext = empty
    if dctx:
        for k in dctx.keys():
            ctx = VariableBinder(ctx, k, parse_type(dctx[k]))
    g = synth_term(listr(l), ctx, parse_type(ty))
    print(g)
    assert g == parse_term(term)


def test_synthesis1():
    helper_syn([0, 0], "Int", "0")


def test_synthesis2():
    helper_syn([1, 0], "Int", "x", {"x": "Int"})


def test_synthesis3():
    helper_syn([1, 1], "Int", "x", {"x": "Int", "y": "{k:Int | k > 0}"})


def test_synthesis4():
    helper_syn([2, 3, 0, 0], "Int", "(\\k -> 0) true")


def test_ref1():
    helper_syn(
        [0, -10],
        "{x:Int | x < 0}",
        "-10",
    )
