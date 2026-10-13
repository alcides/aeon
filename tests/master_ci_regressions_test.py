"""Keep nested inference and generated vector spines within CI bounds."""

import re

import pytest

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Application
from aeon.core.types import AbstractionType, ExistentialType, Kind, TypePolymorphism, TypeVar, t_bool, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.liquid import lower_context, typecheck_liquid
from aeon.utils.name import Name
from scripts.compact_hakank_sequences import compact
from scripts.generate_hakank_examples import Model


def test_nested_application_infers_each_argument_once(monkeypatch):
    import aeon.typechecking.typeinfer as inference

    original = inference._synth
    visits = 0

    def counted(ctx, term):
        nonlocal visits
        if isinstance(term, Application):
            visits += 1
        return original(ctx, term)

    monkeypatch.setattr(inference, "_synth", counted)
    expression = "1"
    depth = 6
    for _ in range(depth):
        expression = f"combine ({expression}) ({expression})"
    source = f"def combine (x:Int) (y:Int) : Int := x + y; def answer : Int := {expression};"
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, check_only=True, no_main=True))
    assert not driver.parse(aeon_code=source)
    assert visits < 8 * 2**depth


def test_targeted_liquid_context_keeps_existential_binders():
    x, wrapper = Name("x", 1), Name("wrapper", 2)
    ctx = TypingContext().with_var(wrapper, ExistentialType(((x, t_int),), t_int))
    assert typecheck_liquid(ctx, LiquidVar(x)) == t_int


def test_targeted_liquid_context_preserves_polymorphic_function_lookup():
    x, f, a = Name("x", 1), Name("f", 2), Name("a", 3)
    ty = TypePolymorphism(a, Kind.BASE, AbstractionType(x, TypeVar(a), t_bool))
    ctx = TypingContext().with_var(f, ty).with_var(x, t_int)
    term = LiquidApp(f, [LiquidLiteralInt(1)])
    assert typecheck_liquid(ctx, term) == t_bool
    assert lower_context(ctx, {f}).functions == {f: [TypeVar(a), t_bool]}


def test_argument_capture_is_reset_after_type_error():
    import aeon.typechecking.typeinfer as inference

    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, check_only=True, no_main=True))
    assert driver.parse(aeon_code='def f (x:Int) : Int := x; def bad : Int := f ("wrong");')
    assert inference._argument_inference.get() is None


@pytest.mark.parametrize("length", [33, 64, 65, 100, 1000])
def test_vector_compaction_preserves_order_and_matches_generator(length):
    source = ""
    tail = "Vec.nil"
    for index in reversed(range(length)):
        name = f"sequence0_tail{index}"
        source += f"def {name} : (Vec Int) := Vec.cons ({index}) ({tail});\n"
        tail = name
    source += "def valid : Bool := Vec.sum sequence0_tail0 = 0;\n"
    result = compact(source)
    assert compact(result) == result
    assert [int(n) for n in re.findall(r"Vec.cons \((\d+)\)", result)] == [
        n for start in reversed(range(0, length, 32)) for n in range(start, min(start + 32, length))
    ]
    model = Model("fixture", "sequence migration")
    model.sequence([str(i) for i in range(length)])
    generated = model.render({"source_url": "https://example.org/fixture"})
    assert [line for line in result.splitlines() if line.startswith("def sequence")] == [
        line for line in generated.splitlines() if line.startswith("def sequence")
    ]


def test_compaction_keeps_shared_or_publicly_referenced_tails():
    source = """def sequence0_tail2 : (Vec Int) := Vec.cons (2) (Vec.nil);
def sequence0_tail1 : (Vec Int) := Vec.cons (1) (sequence0_tail2);
def sequence0_tail0 : (Vec Int) := Vec.cons (0) (sequence0_tail1);
def suffix : (Vec Int) := sequence0_tail1;
"""
    result = compact(source)
    assert "def sequence0_tail1" in result
    assert "def suffix : (Vec Int) := sequence0_tail1;" in result
