"""Unit tests for the FloatHoleNG joint Float-hole synthesizer."""

from __future__ import annotations

import pytest

from aeon.core.substitutions import substitution
from aeon.core.terms import Literal
from aeon.core.types import t_float, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.api import ProgramSynthesizer, SynthesisError
from aeon.synthesis.entrypoint import _make_fitness, synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.float_ng import FloatHoleNGSynthesizer, _is_float
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisFormat

setup_logger()

pytest.importorskip("nevergrad")


def _parse(src: str) -> AeonDriver:
    cfg = AeonConfig(
        synthesizer="ng_float",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=1,
        synthesis_format=SynthesisFormat.DEFAULT,
    )
    driver = AeonDriver(cfg)
    errs = driver.parse(aeon_code=src)
    assert not errs, f"parse/type errors: {errs}"
    return driver


def _synthesize(driver: AeonDriver, synth, budget: float = 2.0) -> dict:
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    return synthesize_holes(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        targets,
        driver.metadata,
        synth,
        budget,
        SilentSynthesisUI(),
    )


def _objective(driver: AeonDriver, mapping: dict) -> float:
    goals = [g for d in driver.metadata.values() for g in d.get("goals", [])]
    prog = driver.core
    for name, term in mapping.items():
        prog = substitution(prog, term, name)
    return float(sum(_make_fitness(g, driver.evaluation_ctx)(prog) for g in goals))


SPHERE = """
def x0 : Float := ?h0;
def x1 : Float := ?h1;
@minimize_float( (x0 * x0) + (x1 * x1) )
def sphere : Float := (x0 * x0) + (x1 * x1);
"""


# ---------------------------------------------------------------------------
# helpers / wiring
# ---------------------------------------------------------------------------


def test_is_float():
    assert _is_float(t_float)
    assert not _is_float(t_int)


def test_is_program_synthesizer():
    assert isinstance(FloatHoleNGSynthesizer(), ProgramSynthesizer)


@pytest.mark.parametrize(
    "name,optimizer",
    [("ng_float", "NGOpt"), ("float_ng", "NGOpt"), ("ng_float_cma", "CMA")],
)
def test_factory_routing(name, optimizer):
    syn = make_synthesizer(name)
    assert isinstance(syn, FloatHoleNGSynthesizer)
    assert syn.optimizer == optimizer


# ---------------------------------------------------------------------------
# end-to-end optimisation
# ---------------------------------------------------------------------------


def test_sphere_converges_near_optimum():
    driver = _parse(SPHERE)
    mapping = _synthesize(driver, FloatHoleNGSynthesizer(optimizer="CMA", seed=1), budget=2.0)
    assert set(h.name for h in mapping) == {"h0", "h1"}
    assert all(isinstance(v, Literal) and v.type == t_float for v in mapping.values())
    # Sphere optimum is 0 at the origin; CMA should get comfortably close.
    assert _objective(driver, mapping) < 0.1


def test_dispatch_through_synthesize_holes():
    # synthesize_holes must route a ProgramSynthesizer to synthesize_program
    # (filling every hole), not the per-hole loop.
    driver = _parse(SPHERE)
    mapping = _synthesize(driver, FloatHoleNGSynthesizer(optimizer="CMA", seed=1), budget=1.0)
    assert len(mapping) == 2


# ---------------------------------------------------------------------------
# precondition errors
# ---------------------------------------------------------------------------


def test_single_hole_rejected():
    src = """
    def x : Float := ?h0;
    @minimize_float( x * x )
    def f : Float := x * x;
    """
    driver = _parse(src)
    with pytest.raises(SynthesisError, match="two or more holes"):
        _synthesize(driver, FloatHoleNGSynthesizer())


def test_non_float_hole_rejected():
    src = """
    def x : Float := ?h0;
    def n : Int := ?h1;
    @minimize_float( (x * x) + 1.0 )
    def f : Float := (x * x) + 1.0;
    """
    driver = _parse(src)
    with pytest.raises(SynthesisError, match="Float"):
        _synthesize(driver, FloatHoleNGSynthesizer())


def test_missing_objective_rejected():
    src = """
    def x0 : Float := ?h0;
    def x1 : Float := ?h1;
    """
    driver = _parse(src)
    with pytest.raises(SynthesisError, match="objective"):
        _synthesize(driver, FloatHoleNGSynthesizer())
