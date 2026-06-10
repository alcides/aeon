"""Axioms via ``def`` + ``native`` in the ``LearningLines`` library.

A ``native`` body is trusted (not checked against its declared
refinement), so ``def ax (...) : {u: Unit | P} = native "()"`` asserts
``P`` as an axiom. Because Aeon refinements are quantifier-free, the
axiom is brought into a proof by *instantiating* it — calling it with the
relevant arguments. These tests check that each Appendix-A axiom in
``libraries/LearningLines.ae`` is **load-bearing**: the proof type-checks
when the axiom is instantiated and is rejected when it is not.
"""

from __future__ import annotations

from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.synthesis.uis.api import SilentSynthesisUI


def _typechecks(source: str) -> bool:
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    return not errors


# Each case is a (proof-with-instantiation, proof-without-instantiation)
# pair sharing the same signature; only the ``let inst = ...`` line differs.

_TIMESERIES = """
open LearningLines
def thm
    (d: LDataset) (earlier: Line) (later: Line)
    (h: {{x: Int | line_count d > 1 && is_ts d && earlier != later && prec earlier later d}}) :
    {{r: Int | causality earlier later}} :=
    {body} ;
"""

_PREC_TRANS = """
open LearningLines
def thm
    (d: LDataset) (a: Line) (b: Line) (c: Line)
    (h: {{x: Int | a != b && b != c && a != c && prec a b d && prec b c d}}) :
    {{r: Int | prec a c d}} :=
    {body} ;
"""

_ANTISYM = """
open LearningLines
def thm
    (a: Line) (b: Line)
    (h: {{x: Int | causality a b && causality b a}}) :
    {{r: Int | false}} :=
    {body} ;
"""

_CLONE = """
open LearningLines
def thm
    (a: Line) (b: Line)
    (h: {{x: Int | clone a b}}) :
    {{r: Int | causality a b}} :=
    {body} ;
"""

CASES = {
    "timeseries": (_TIMESERIES, "let inst := LearningLines.ax_timeseries earlier later d in h"),
    "prec_trans": (_PREC_TRANS, "let inst := LearningLines.ax_prec_trans a b c d in h"),
    "antisym": (_ANTISYM, "let inst := LearningLines.ax_causality_antisym a b in h"),
    "clone": (_CLONE, "let inst := LearningLines.ax_clone_causality a b in h"),
}


def test_axioms_discharge_when_instantiated():
    for name, (template, instantiated) in CASES.items():
        assert _typechecks(template.format(body=instantiated)), f"{name}: should type-check with the axiom instantiated"


def test_proofs_fail_without_the_axiom():
    # Same signature, but the conclusion is asserted with no axiom in
    # scope — the uninterpreted relations leave it unprovable.
    for name, (template, _instantiated) in CASES.items():
        assert not _typechecks(template.format(body="h")), f"{name}: should be rejected without the axiom"
