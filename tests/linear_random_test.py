"""Linear pseudo-random generators (``libraries/Random.ae``, issue #441).

Randomness is threaded through a generator used at multiplicity 1, so a draw
is never a pure (referentially transparent) function. These tests check that
the refinement on a drawn value composes into proofs, that the bound is
tight, that the linear discipline is enforced (a generator must be used
exactly once), and that the polymorphic ``with_choice`` continuation works.
"""

from __future__ import annotations

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _errors(source: str):
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    return list(AeonDriver(cfg).parse(aeon_code=source))


def _typechecks(source: str) -> bool:
    return not _errors(source)


_TWO_DICE = """
open Random
def two_dice (seed: Int) : {s:Int | s >= 2 && s <= %s} :=
    let 1 g0 := new_rng seed in
    let d1 := draw_int 1 6 g0 in
    let a := int_value 1 6 d1 in
    let 1 g1 := int_next d1 in
    let d2 := draw_int 1 6 g1 in
    let b := int_value 1 6 d2 in
    let 1 g2 := int_next d2 in
    let _ : Unit := close_rng g2 in
    a + b
def main (x:Int) : Unit := print (two_dice 1) ;
"""


def test_drawn_bound_composes_into_proof():
    # Two dice each in [1, 6] provably sum to [2, 12].
    assert _typechecks(_TWO_DICE % "12")


def test_bound_is_tight():
    # 12 is reachable, so a declared upper bound of 11 must be rejected.
    assert not _typechecks(_TWO_DICE % "11")


def test_generator_must_be_used():
    # Forgetting to consume the final successor `g2` is a linearity error.
    src = """
    open Random
    def one_die (seed: Int) : {s:Int | s >= 1 && s <= 6} :=
        let 1 g0 := new_rng seed in
        let d1 := draw_int 1 6 g0 in
        let a := int_value 1 6 d1 in
        let 1 g1 := int_next d1 in
        a
    def main (x:Int) : Unit := print (one_die 1) ;
    """
    assert not _typechecks(src)


def test_generator_cannot_be_reused():
    # Drawing from the same generator twice violates multiplicity 1.
    src = """
    open Random
    def main (seed: Int) : Unit :=
        let 1 g0 := new_rng seed in
        let d1 := draw g0 in
        let d2 := draw g0 in
        let 1 g1 := draw_next d1 in
        close_rng g1 ;
    """
    assert not _typechecks(src)


def test_float_draw_refinement():
    # `draw_value` yields a float in [0.0, 1.0); claiming >= 0.5 must fail.
    bad = """
    open Random
    def f (seed: Int) : {r:Float | r >= 0.5} :=
        let 1 g0 := new_rng seed in
        let d := draw g0 in
        let x := draw_value d in
        let 1 g1 := draw_next d in
        let _ : Unit := close_rng g1 in
        x
    def main (x:Int) : Unit := print (f 1) ;
    """
    assert not _typechecks(bad)


def test_polymorphic_choice():
    src = """
    open Random
    open Array
    def pick (seed: Int) : Int :=
        let 1 g0 := new_rng seed in
        with_choice #[10, 20, 30] g0 (fun x => fun g1 =>
            let _ : Unit := close_rng g1 in
            x)
    def main (x:Int) : Unit := print (pick 3) ;
    """
    assert _typechecks(src)


def test_two_dice_runs_in_range():
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=False,
    )
    driver = AeonDriver(cfg)
    src = """
    open Random
    def two_dice (seed: Int) : {s:Int | s >= 2 && s <= 12} :=
        let 1 g0 := new_rng seed in
        let d1 := draw_int 1 6 g0 in
        let a := int_value 1 6 d1 in
        let 1 g1 := int_next d1 in
        let d2 := draw_int 1 6 g1 in
        let b := int_value 1 6 d2 in
        let 1 g2 := int_next d2 in
        let _ : Unit := close_rng g2 in
        a + b
    def main (x:Int) : Int := two_dice 7 ;
    """
    assert not driver.parse(aeon_code=src)
    result = driver.run()
    assert 2 <= result <= 12
