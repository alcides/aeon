from aeon.typing.well_formed import inhabited
import random
from typing import Dict
from aeon.core.substitutions import liquefy
from aeon.typing.context import EmptyContext, TypingContext, VariableBinder
from aeon.synthesis.term_synthesis import NoMoreBudget, synth_term
from aeon.synthesis.type_synthesis import synth_type, synth_liquid
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


def helper_syn_type(l, ty: str, dctx: Dict[str, str] = None):
    ctx: TypingContext = empty
    if dctx:
        for k in dctx.keys():
            ctx = VariableBinder(ctx, k, parse_type(dctx[k]))
    t = synth_type(listr(l), ctx)
    print("GOT TYPE:", t)
    assert t == parse_type(ty)


def helper_syn_liq(l, t: str, liq: str, dctx: Dict[str, str] = None):
    ctx: TypingContext = empty
    if dctx:
        for k in dctx.keys():
            ctx = VariableBinder(ctx, k, parse_type(dctx[k]))

    s = synth_liquid(listr(l), ctx, parse_type(t))
    liq_term = parse_term(liq)
    expected = liquefy(liq_term)
    assert s == expected


def helper_syn(l, ty: str, term: str, dctx: Dict[str, str] = None):
    ctx: TypingContext = empty
    if dctx:
        for k in dctx.keys():
            ctx = VariableBinder(ctx, k, parse_type(dctx[k]))
    type_ = parse_type(ty)
    if inhabited(ctx, type_):
        try:
            g = synth_term(listr(l), ctx, type_)
            print(g, "DEBUG")
            assert g == parse_term(term)
        except NoMoreBudget as e:
            pass


def test_synthesis1():
    helper_syn([0, 0], "Int", "0")


def test_synthesis2():
    helper_syn([1, 0], "Int", "x", {"x": "Int"})


def test_synthesis3():
    helper_syn([1, 1], "Int", "x", {"x": "Int", "y": "{k:Int | k > 0}"})


def test_synthesis4():
    helper_syn([2, 3, 0, 0], "Int", "(\\fresh_1 -> 0) 2")


def test_ref1():
    helper_syn(
        [0, -10],
        "{x:Int | x < 0}",
        "-10",
    )


def test_ref2():
    helper_syn(
        rseed,
        "{x:Int | x >= 0}",
        "49557",
    )


def test_t():
    helper_syn_type([0, 0, 0, 1, 0, 0, 0, 400] + rseed, "Int")


def test_liq_term():
    helper_syn_liq([0, 0] + rseed, "Bool", "x", {"x": "Bool"})
    helper_syn_liq([0, 0] + rseed, "Int", "x", {"x": "Int"})
    helper_syn_liq([0, 0] + rseed, "Bool", "y", {"x": "Int", "y": "Bool"})

    helper_syn_liq([1, 0] + rseed, "Bool", "true")
    helper_syn_liq([1, 1] + rseed, "Bool", "false")
    helper_syn_liq([1, 80] + rseed, "Int", "80")
    helper_syn_liq([1, 91] + rseed, "Int", "91")


def test_liq_app():
    d = {"x": "Bool", "y": "Int", "z": "Bool", "w": "Int"}
    helper_syn_liq([2, 0, 0, 1, 2, 3, 4], "Bool", "2 == w", d)
    helper_syn_liq([2, 5, 4, 3, 2, 1, 4, 5, 6, 7] + rseed, "Int", "3 * (5 + y)", d)


def test_liq_term_r1000():
    for i in range(1000):
        seed = [random.randint(0, 100) for _ in range(20)] + rseed
        s = synth_liquid(
            listr(seed),
            VariableBinder(EmptyContext(), "x", parse_type("Int")),
            parse_type("Int"),
        )
        assert s != None
