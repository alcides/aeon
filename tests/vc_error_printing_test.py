"""Integration tests for VC decomposition used in error messages."""

from __future__ import annotations

from aeon.core.bind import bind_lq
from aeon.core.types import t_int
from aeon.facade.api import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.typeinfer import constraint_to_parts
from aeon.utils.name import Name
from aeon.verification.helpers import liquid_terms_alpha_equal
from aeon.verification.helpers import parse_liquid, pretty_print_constraint
from aeon.verification.vcs import Implication, LiquidConstraint


def _errors(source: str):
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    return list(AeonDriver(cfg).parse(aeon_code=source))


def _liquid_failures(source: str) -> list[LiquidTypeCheckingFailedRelation]:
    return [e for e in _errors(source) if isinstance(e, LiquidTypeCheckingFailedRelation)]


def test_constraint_to_parts_yields_only_failing_and_conjunct():
    """When only one supertype conjunct fails, only that sub-VC is reported."""
    x_name = Name("x", 0)
    pred = bind_lq(parse_liquid("x > 0"), [("x", x_name)])
    concl = bind_lq(parse_liquid("x > 1 && x > 0"), [("x", x_name)])

    c = Implication(x_name, t_int, pred, LiquidConstraint(concl))
    parts = list(constraint_to_parts(c))

    assert len(parts) == 1
    vc, _ = parts[0]
    assert isinstance(vc, Implication)
    expected = bind_lq(parse_liquid("x > 1"), [("x", x_name)])
    assert liquid_terms_alpha_equal(vc.seq.expr, expected)


def test_constraint_to_parts_yields_both_failing_and_conjuncts():
    """When every supertype conjunct fails, each failing sub-VC is reported."""
    x_name = Name("x", 0)
    pred = bind_lq(parse_liquid("true"), [("x", x_name)])
    concl = bind_lq(parse_liquid("x > 10 && x < 5"), [("x", x_name)])

    c = Implication(x_name, t_int, pred, LiquidConstraint(concl))
    parts = list(constraint_to_parts(c))

    assert len(parts) == 2
    goals = [vc.seq.expr for vc, _ in parts if isinstance(vc, Implication)]
    expected = [
        bind_lq(parse_liquid("x > 10"), [("x", x_name)]),
        bind_lq(parse_liquid("x < 5"), [("x", x_name)]),
    ]
    for goal in goals:
        assert any(liquid_terms_alpha_equal(goal, exp) for exp in expected)
    for exp in expected:
        assert any(liquid_terms_alpha_equal(goal, exp) for goal in goals)


def test_error_message_omits_irrelevant_preconditions():
    src = """
def my_len: (s:String) -> Int := uninterpreted;

def claim (x:Int) : {r:Int | r >= x} :=
    x - 10;
"""
    failures = _liquid_failures(src)
    assert failures
    rendered = pretty_print_constraint(failures[0].vc)
    assert "len" not in rendered


def test_error_message_keeps_relevant_precondition():
    src = """
open Math
def f (n:Int) : Float := Math.sqrt n
def main (a:Int) : Unit := print (f a) ;
"""
    failures = _liquid_failures(src)
    assert failures
    rendered = str(failures[0])
    assert "counterexample:" in rendered
    assert "n =" in rendered


def test_valid_program_has_no_vc_errors():
    assert not _liquid_failures("def ok (x:Int) : {v:Int | v = x + x} := x + x ;")
