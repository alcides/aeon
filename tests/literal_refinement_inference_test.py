"""Plain constructor literals need no qualifier search; contracts still do."""

import pytest

from aeon.core.liquid import LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.types import LiquidHornApplication, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name
from aeon.verification import horn
from aeon.verification.helpers import parse_liquid
from aeon.verification.vcs import Conjunction, Implication, LiquidConstraint


def parse(source):
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=True))
    return driver.parse(aeon_code=source)


def test_nested_inline_literals_do_not_enumerate_qualifiers(monkeypatch):
    def unexpected(*args, **kwargs):
        pytest.fail("plain list literals should not require qualifier enumeration")

    monkeypatch.setattr(horn, "build_initial_assignment", unexpected)
    rows = "[" + ", ".join("[1, 2, 3, 4, 5, 6, 7, 8]" for _ in range(8)) + "]"
    assert not parse(f"import List; @example(f {rows} = 8) def f (xs:(List (List Int))) : Int := ?h;")


@pytest.mark.parametrize("seed, valid", [(3, True), (-3, False)])
def test_predicate_dependencies_fall_back_to_inference(monkeypatch, seed, valid):
    original = horn.build_initial_assignment
    searches = []

    def record(*args, **kwargs):
        searches.append(True)
        return original(*args, **kwargs)

    monkeypatch.setattr(horn, "build_initial_assignment", record)
    x, first, second = Name("x"), Name("first"), Name("second")
    p = LiquidHornApplication(first, [(LiquidVar(x), t_int)])
    q = LiquidHornApplication(second, [(LiquidVar(x), t_int)])
    seed_clause = LiquidConstraint(LiquidHornApplication(first, [(LiquidLiteralInt(seed), t_int)]))
    propagation = Implication(x, t_int, p, LiquidConstraint(q))
    required = Implication(x, t_int, q, LiquidConstraint(parse_liquid("x >= 0")))
    assert horn.solve(Conjunction(seed_clause, Conjunction(propagation, required))) == valid
    assert searches, "a nontrivial inferred predicate is necessary here"


def test_default_predicate_cannot_discard_a_false_obligation():
    unknown = LiquidConstraint(LiquidHornApplication(Name("unused"), [(LiquidLiteralInt(1), t_int)]))
    assert not horn.solve(Conjunction(unknown, LiquidConstraint(LiquidLiteralBool(False))))


def test_independent_false_obligation_does_not_enumerate_qualifiers(monkeypatch):
    def unexpected(*args, **kwargs):
        pytest.fail("inference cannot repair a predicate with no unknowns")

    monkeypatch.setattr(horn, "build_initial_assignment", unexpected)
    source = """
import List
def same_length (xs:(List Int)) (ys:{v:(List Int) | List.size v = List.size xs}) : Bool := ?h;
def mismatch : Bool := same_length [1, 2, 3] [1, 2];
"""
    assert parse(source)


@pytest.mark.parametrize("length, valid", [(3, True), (4, False)])
def test_literal_length_refinement_is_preserved(length, valid):
    source = f"import List; def xs : {{v:(List Int) | List.size v = {length}}} := [1, 2, 3];"
    assert (not parse(source)) == valid
