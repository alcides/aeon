from aeon.synthesis.choice_manager import ChoiceManager, DynamicProbManager
from aeon.typing.well_formed import inhabited
import random
from typing import Dict, Union, List
from aeon.core.substitutions import liquefy
from aeon.typing.context import EmptyContext, TypingContext, VariableBinder
from aeon.synthesis.exceptions import NoMoreBudget
from aeon.synthesis.term_synthesis import synth_term
from aeon.synthesis.type_synthesis import synth_type, synth_liquid
from aeon.synthesis.sources import ListRandomSource, RandomSource, SeededRandomSource
from aeon.frontend.parser import parse_type, parse_term
from aeon.utils.ctx_helpers import build_context

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
    man: ChoiceManager = DynamicProbManager()
    if dctx:
        for k in dctx.keys():
            ctx = VariableBinder(ctx, k, parse_type(dctx[k]))
    t = synth_type(man, listr(l), ctx)
    assert t == parse_type(ty)


def helper_syn_liq(l, t: str, liq: str, dctx: Dict[str, str] = None):
    man: ChoiceManager = ChoiceManager()
    ctx: TypingContext = empty
    if dctx:
        for k in dctx.keys():
            ctx = VariableBinder(ctx, k, parse_type(dctx[k]))

    s = synth_liquid(man, listr(l), ctx, parse_type(t))
    liq_term = parse_term(liq)
    expected = liquefy(liq_term)
    assert s == expected


def helper_syn(
    l: Union[List[int], RandomSource],
    ty: str,
    term: str,
    dctx: Dict[str, str] = None,
    budget=50,
):
    man: ChoiceManager = ChoiceManager()
    randomSource: RandomSource
    if isinstance(l, list):
        randomSource = listr(l)
    else:
        randomSource = l
    ctx: TypingContext = empty
    if dctx:
        for k in dctx.keys():
            ctx = VariableBinder(ctx, k, parse_type(dctx[k]))
    type_ = parse_type(ty)
    if inhabited(ctx, type_):
        try:
            g = synth_term(man, randomSource, ctx, type_, d=budget)
            assert g == parse_term(term)
        except NoMoreBudget as e:
            pass
            assert False
    else:
        assert False


def test_synthesis1():
    helper_syn([0, 0], "Int", "0")


def test_synthesis2():
    helper_syn([1, 0], "Int", "x", {"x": "Int"})


def test_synthesis3():
    helper_syn([1, 1], "Int", "x", {"x": "Int", "y": "{k:Int | k > 0}"})


def test_synthesis4():
    helper_syn(
        [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1],
        "Int",
        r"((\fresh_1 -> fresh_1) 0)",
    )


def test_ref1():
    helper_syn(
        [0, -1],
        "{x:Int | x < 0}",
        "-1",
    )


def test_ref2():
    helper_syn([400, 500, 600, -700], "{x:Int | x >= 0}", "0", budget=100)


def test_ref3():
    helper_syn(
        [0, 1] + rseed,
        "{x:Int | x == 3}",
        "3",
    )


def test_t():
    helper_syn_type([0, 0, 0, 1, 0, 0, 0, 400] + rseed, "Int")


def test_liq_term1():
    helper_syn_liq([1, 0] + rseed, "Bool", "x", {"x": "Bool"})


def test_liq_term2():
    helper_syn_liq([1, 0] + rseed, "Int", "x", {"x": "Int"})


def test_liq_term3():
    helper_syn_liq([1, 0] + rseed, "Bool", "y", {"x": "Int", "y": "Bool"})


def test_liq_term4():
    helper_syn_liq([0, 0] + rseed, "Bool", "true")


def test_liq_term5():
    helper_syn_liq([0, 1] + rseed, "Bool", "false")


def test_liq_term6():
    helper_syn_liq([0, 80] + rseed, "Int", "80")


def test_liq_term7():
    helper_syn_liq([0, 91] + rseed, "Int", "91")


def test_liq_app():
    d = {"x": "Bool", "y": "Int", "z": "Bool", "w": "Int"}
    helper_syn_liq([2, 0, 0, 0, 2, 1, 4], "Bool", "2 == w", d)
    helper_syn_liq([2, 5, 4, 3, 2, 1, 4, 5, 6, 7] + rseed, "Int", "y * (y + 7)", d)


def test_liq_term_r1000():
    for i in range(1000):
        man = ChoiceManager()
        seed = [random.randint(0, 100) for _ in range(20)] + rseed
        s = synth_liquid(
            man,
            listr(seed),
            VariableBinder(EmptyContext(), "x", parse_type("Int")),
            parse_type("Int"),
        )
        assert s != None


def test_can_generate_plus():
    ctx = build_context({"plus": parse_type("(x:Int) -> Int")})
    seed = [1, 3, 4, 0, 1, 3, 1]
    s = synth_term(ChoiceManager(), listr(seed), ctx, parse_type("Int"), 5)
    assert s == parse_term("plus 1")


def test_can_generate_plus2():
    ctx = build_context({"plus": parse_type("(x:Int) -> (y:Int) -> Int")})
    seed = [0]
    s = synth_term(
        ChoiceManager(), listr(seed), ctx, parse_type("(k:Int) -> (z:Int) -> Int"), 3
    )
    assert s == parse_term("plus")


def test_can_generate_plus3():
    ctx = build_context({"plus": parse_type("(x:Int) -> (y:Int) -> {x:Int | x == 0 }")})
    seed = [1, 1, 2, 0, 1, 0, 0, 2, 3]
    s = synth_term(ChoiceManager(), listr(seed), ctx, parse_type("Int"), 3)
    assert s == parse_term("(plus 1) 2")
