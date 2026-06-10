"""The Lean-style ``axiom`` keyword.

``axiom name : <type> ;`` introduces a trusted constant of the given
(possibly dependent, refined) type. Its refinements are assumed and never
checked. Because Aeon's refinements are quantifier-free, an axiom is used
by *instantiating* it — applying it to concrete arguments brings its fact
into the proof context. These tests check that an axiom is load-bearing
(discharges an obligation only when instantiated) and that the various
binder shapes parse and elaborate.
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


def test_axiom_discharges_when_instantiated():
    src = """
    def p : (x:Int) -> Bool := uninterpreted
    axiom assume_p : (x:Int) -> {u:Unit | p x = true} ;
    def needs_p (y: {z:Int | p z = true}) : Int := y ;
    def main (a:Int) : Int :=
        let inst := assume_p 5 in
        needs_p 5 ;
    """
    assert _typechecks(src)


def test_axiom_is_load_bearing():
    # Same program, but the axiom is never instantiated, so the fact is
    # not in scope and the precondition cannot be discharged.
    src = """
    def p : (x:Int) -> Bool := uninterpreted
    axiom assume_p : (x:Int) -> {u:Unit | p x = true} ;
    def needs_p (y: {z:Int | p z = true}) : Int := y ;
    def main (a:Int) : Int := needs_p 5 ;
    """
    assert not _typechecks(src)


def test_relational_axiom_transitivity():
    src = """
    def prec : (a:Int) -> (b:Int) -> Bool := uninterpreted
    axiom trans :
        (a:Int) -> (b:Int) -> (c:Int) -> {u:Unit | (prec a b && prec b c) --> prec a c} ;
    def use (a: {x:Int | prec 1 2 && prec 2 3}) : {r:Int | prec 1 3} :=
        let l := trans 1 2 3 in a ;
    def main (a:Int) : Int := 0 ;
    """
    assert _typechecks(src)


def test_polymorphic_axiom_with_forall():
    src = """
    def q : forall a:B, (x:a) -> Bool := uninterpreted
    axiom q_holds : forall a:B, (x:a) -> {u:Unit | q x = true} ;
    def needs (n: {z:Int | q z = true}) : Int := n ;
    def main (a:Int) : Int := let i := q_holds 7 in needs 7 ;
    """
    assert _typechecks(src)


def test_constant_axiom_no_arguments():
    # An axiom need not be a function: a bare refined constant (zero binders)
    # works too, stating a closed fact about an uninterpreted symbol.
    src = """
    def p : (x:Int) -> Bool := uninterpreted
    axiom p_at_5 : {u:Unit | p 5 = true} ;
    def needs (n: {z:Int | p 5 = true}) : Int := n ;
    def main (a:Int) : Int :=
        let fact := p_at_5 in
        needs 0 ;
    """
    assert _typechecks(src)
