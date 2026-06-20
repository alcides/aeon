"""Unit tests for the IntHoleCP (OR-Tools CP-SAT) synthesizer."""

from __future__ import annotations

import pytest

from aeon.core.terms import Literal
from aeon.core.types import t_float, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.api import ProgramSynthesizer, SynthesisError
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer, _array_elem, _is_float, _is_int
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisFormat

setup_logger()

pytest.importorskip("ortools")


def _parse(src: str) -> AeonDriver:
    cfg = AeonConfig(
        synthesizer="ortools",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=1,
        synthesis_format=SynthesisFormat.DEFAULT,
    )
    driver = AeonDriver(cfg)
    errs = driver.parse(aeon_code=src)
    assert not errs, f"parse/type errors: {errs}"
    return driver


def _solve(driver: AeonDriver, budget: float = 8.0) -> dict:
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    return synthesize_holes(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        targets,
        driver.metadata,
        CPSatHoleSynthesizer(bound=50),
        budget,
        SilentSynthesisUI(),
    )


def _values(mapping: dict) -> dict:
    return {name.name: term.value for name, term in mapping.items()}


# ---------------------------------------------------------------------------
# helpers / wiring
# ---------------------------------------------------------------------------


def test_is_int():
    assert _is_int(t_int)
    assert not _is_int(t_float)


def test_type_classifiers():
    from aeon.core.types import TypeConstructor
    from aeon.utils.name import Name

    assert _is_float(t_float)
    assert _array_elem(TypeConstructor(Name("Array", 0), [t_int])) == "int"
    assert _array_elem(TypeConstructor(Name("Array", 0), [t_float])) == "float"
    assert _array_elem(t_int) is None


def test_is_program_synthesizer():
    assert isinstance(CPSatHoleSynthesizer(), ProgramSynthesizer)


@pytest.mark.parametrize("name", ["ortools", "ortools_int", "cpsat"])
def test_factory_routing(name):
    assert isinstance(make_synthesizer(name), CPSatHoleSynthesizer)


# ---------------------------------------------------------------------------
# exact optimisation
# ---------------------------------------------------------------------------


def test_int_sphere_exact_optimum():
    src = """
    def x : {v:Int | v > 0 - 50 && v < 50} := ?hx;
    def y : {v:Int | v > 0 - 50 && v < 50} := ?hy;
    @minimize_int( (x * x) + (y * y) )
    def isphere : Int := (x * x) + (y * y);
    """
    mapping = _solve(_parse(src))
    assert all(isinstance(v, Literal) and v.type == t_int for v in mapping.values())
    assert _values(mapping) == {"hx": 0, "hy": 0}


def test_int_booth_exact_optimum():
    src = """
    def x : {v:Int | v > 0 - 20 && v < 20} := ?hx;
    def y : {v:Int | v > 0 - 20 && v < 20} := ?hy;
    @minimize_int( (((x + (2 * y)) - 7) * ((x + (2 * y)) - 7)) + ((((2 * x) + y) - 5) * (((2 * x) + y) - 5)) )
    def booth : Int := (((x + (2 * y)) - 7) * ((x + (2 * y)) - 7)) + ((((2 * x) + y) - 5) * (((2 * x) + y) - 5));
    """
    assert _values(_solve(_parse(src))) == {"hx": 1, "hy": 3}


def test_refinement_constrains_optimum():
    # Unconstrained optimum is x = 3, but x is refined to [5, 20]; CP-SAT must
    # return the feasible optimum x = 5.
    src = """
    def x : {v:Int | v >= 5 && v <= 20} := ?hx;
    def y : {v:Int | v >= 5 && v <= 20} := ?hy;
    @minimize_int( ((x - 3) * (x - 3)) + ((y - 3) * (y - 3)) )
    def f : Int := ((x - 3) * (x - 3)) + ((y - 3) * (y - 3));
    """
    assert _values(_solve(_parse(src))) == {"hx": 5, "hy": 5}


def test_let_bound_holes_inside_function():
    # Holes are `let`-bound inside `f`, and the objective is `f` itself: the
    # translator must descend the lets and inline `f` to reach both holes.
    src = """
    @minimize_int( f )
    def f : Int :=
      let x : Int | x >= 5 && x <= 20 := ?hx in
      let y : Int | y >= 0 - 5 && y <= 12 := ?hy in
      ((x - 3) * (x - 3)) + ((y - 30) * (y - 30));
    """
    mapping = _solve(_parse(src))
    assert _values(mapping) == {"hx": 5, "hy": 12}


def test_maximize():
    src = """
    def x : {v:Int | v >= 0 && v <= 7} := ?hx;
    def y : {v:Int | v >= 0 && v <= 7} := ?hy;
    @maximize_int( x + y )
    def f : Int := x + y;
    """
    assert _values(_solve(_parse(src))) == {"hx": 7, "hy": 7}


def test_float_holes_fixed_point():
    # CP-SAT models Float in fixed point; the optimum (2.5, -1.25) lies on the
    # 1/1000 grid, so it is recovered exactly.
    src = """
    def x : {v:Float | v >= 0.0 - 5.0 && v <= 5.0} := ?hx;
    def y : {v:Float | v >= 0.0 - 5.0 && v <= 5.0} := ?hy;
    @minimize_float( ((x - 2.5) * (x - 2.5)) + ((y + 1.25) * (y + 1.25)) )
    def f : Float := ((x - 2.5) * (x - 2.5)) + ((y + 1.25) * (y + 1.25));
    """
    mapping = _solve(_parse(src))
    assert all(isinstance(v, Literal) and v.type == t_float for v in mapping.values())
    assert _values(mapping) == {"hx": 2.5, "hy": -1.25}


def test_array_int_hole():
    src = """
    import Array;
    @minimize_int( (((Array.get v 0) - 3) * ((Array.get v 0) - 3)) + (((Array.get v 1) + 7) * ((Array.get v 1) + 7)) )
    def v : {a:(Array Int) | Array.size a = 2} := ?h;
    """
    mapping = _solve(_parse(src))
    (term,) = mapping.values()
    assert isinstance(term.value, list) and term.value == [3, -7]


def test_array_float_hole():
    src = """
    import Array;
    @minimize_float( (((Array.get v 0) - 1.5) * ((Array.get v 0) - 1.5)) + (((Array.get v 1) + 2.25) * ((Array.get v 1) + 2.25)) )
    def v : {a:(Array Float) | Array.size a = 2} := ?h;
    """
    mapping = _solve(_parse(src))
    (term,) = mapping.values()
    assert term.value == [1.5, -2.25]


# ---------------------------------------------------------------------------
# precondition / unsupported-fragment errors
# ---------------------------------------------------------------------------


def test_non_numeric_hole_rejected():
    # Bool holes are outside the numeric fragment CP-SAT can model.
    src = """
    def b : Bool := ?hb;
    def x : {v:Int | v >= 0 && v <= 5} := ?hx;
    @minimize_int( x * x )
    def f : Int := x * x;
    """
    with pytest.raises(SynthesisError, match="cannot handle hole"):
        _solve(_parse(src))


def test_unsupported_objective_rejected():
    # Integer division is outside the translatable fragment.
    src = """
    def x : {v:Int | v >= 1 && v <= 9} := ?hx;
    def y : {v:Int | v >= 1 && v <= 9} := ?hy;
    @minimize_int( (x / y) + 1 )
    def f : Int := (x / y) + 1;
    """
    with pytest.raises(SynthesisError, match="objective"):
        _solve(_parse(src))
