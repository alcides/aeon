"""Linear batch samplers in ``libraries/Distributions.ae`` (issue #441 follow-up)."""

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


_CHAIN = """
open Random
open Distributions
def chain (seed: Int) : {xs: (Array Float) | Array.size xs > 0} :=
    let 1 g0 := new_rng seed in
    let nd := normal_sample g0 2.0 1.0 10 in
    let xs := normal_value 2.0 1.0 nd in
    let 1 g1 := sample_next nd in
    let ud := uniform_sample g1 0.0 1.0 10 in
    uniform_value 0.0 1.0 ud
def main (x:Int) : Unit := print 0 ;
"""


def test_distribution_chain_typechecks():
    assert _typechecks(_CHAIN)


def test_unextracted_successor_needs_no_close():
    # Like scalar draws, stopping after projecting the sample is fine.
    src = """
    open Random
    open Distributions
    def one_batch (seed: Int) : {xs: (Array Float) | Array.size xs > 0} :=
        let 1 g0 := new_rng seed in
        let nd := normal_sample g0 2.0 1.0 10 in
        normal_value 2.0 1.0 nd
    def main (x:Int) : Unit := print 0 ;
    """
    assert _typechecks(src)


def test_extracted_successor_must_be_used():
    src = """
    open Random
    open Distributions
    def bad (seed: Int) : {xs: (Array Float) | Array.size xs > 0} :=
        let 1 g0 := new_rng seed in
        let nd := normal_sample g0 2.0 1.0 10 in
        let xs := normal_value 2.0 1.0 nd in
        let 1 g1 := sample_next nd in
        xs
    def main (x:Int) : Unit := print 0 ;
    """
    assert not _typechecks(src)


def test_poisson_batch_helper():
    import random

    from aeon.bindings.random_sample import poisson_batch

    g = random.Random(0)
    xs = poisson_batch(3.0, 50, g)
    assert len(xs) == 50
    assert all(x >= 0.0 for x in xs)


def test_distributions_demo_runs():
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=False,
    )
    driver = AeonDriver(cfg)
    src = open("examples/probabilistic/distributions_demo.ae").read()
    assert not driver.parse(aeon_code=src)
    driver.run()  # should not raise
