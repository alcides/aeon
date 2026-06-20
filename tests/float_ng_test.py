"""Unit tests for the FloatHoleNG joint Float-hole synthesizer."""

from __future__ import annotations

import pytest

from aeon.core.substitutions import substitution
from aeon.core.terms import Literal
from aeon.core.types import TypeConstructor, t_float, t_int
from aeon.utils.name import Name
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.api import ProgramSynthesizer, SynthesisError
from aeon.synthesis.entrypoint import _make_fitness, synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.types import RefinedType
from aeon.synthesis.modules.float_ng import (
    FloatHoleNGSynthesizer,
    _array_length,
    _is_array_float,
    _is_float,
)
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
    with pytest.raises(SynthesisError, match="dimension"):
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


# ---------------------------------------------------------------------------
# Array Float holes
# ---------------------------------------------------------------------------


def test_is_array_float():
    assert _is_array_float(TypeConstructor(Name("Array", 0), [t_float]))
    assert not _is_array_float(TypeConstructor(Name("Array", 0), [t_int]))
    assert not _is_array_float(t_float)


ARRAY_SPHERE = """
import Array (size, get)
def v : {a:(Array Float) | size a == 3} = ?h;
@minimize_float( ((get v 0) * (get v 0)) + ((get v 1) * (get v 1)) + ((get v 2) * (get v 2)) )
def sphere : Float = ((get v 0) * (get v 0)) + ((get v 1) * (get v 1)) + ((get v 2) * (get v 2));
"""


def test_array_float_hole_converges():
    driver = _parse(ARRAY_SPHERE)
    mapping = _synthesize(driver, FloatHoleNGSynthesizer(optimizer="CMA", seed=1), budget=3.0)
    assert len(mapping) == 1
    (term,) = mapping.values()
    # The single (Array Float) hole is filled with a length-3 list literal.
    assert isinstance(term, Literal)
    assert isinstance(term.value, list) and len(term.value) == 3
    assert _objective(driver, mapping) < 0.1


def _array_refined(refinement) -> RefinedType:
    return RefinedType(Name("a", 0), TypeConstructor(Name("Array", 0), [t_float]), refinement)


def _size_eq(left_int: bool, k: int) -> LiquidApp:
    size = LiquidApp(Name("Array_size", 0), [LiquidVar(Name("a", 0))])
    lit = LiquidLiteralInt(k)
    args = [lit, size] if left_int else [size, lit]
    return LiquidApp(Name("==", 0), args)


def test_array_length_extracts_size():
    assert _array_length(_array_refined(_size_eq(False, 4))) == 4


def test_array_length_reversed_operands():
    assert _array_length(_array_refined(_size_eq(True, 7))) == 7


def test_array_length_none_without_fixed_size():
    # `size a > 0` constrains but does not fix the length → no dimension count.
    refinement = LiquidApp(
        Name(">", 0),
        [LiquidApp(Name("Array_size", 0), [LiquidVar(Name("a", 0))]), LiquidLiteralInt(0)],
    )
    assert _array_length(_array_refined(refinement)) is None
