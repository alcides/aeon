"""Conservative typechecking evidence loss must not become synthesis UNSAT."""

import json

import pytest

from aeon.benchmarks.bounded_boolean.checker import check, extract
from aeon.benchmarks.bounded_boolean.corpus import ROOT, load_case
from aeon.core.liquid import LiquidApp, liquid_free_vars
from aeon.core.terms import Application, Var
from aeon.core.types import AbstractionType, t_bool
from aeon.synthesis.modules.boolean_bounded import BooleanBoundedSynthesizer
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import _selfification_liquid, exact_application_identities
from aeon.utils.name import Name
from tests.boolean_bounded_test import call
from tests.joint_hole_synthesis_test import parse, solve, fill


def test_exact_identity_mode_is_scoped_even_after_errors():
    xs = [Name(f"x{i}", i + 1) for i in range(40)]
    name = Name("many", 100)
    ty = t_bool
    term = Var(name)
    ctx = TypingContext()
    for x in reversed(xs):
        ty = AbstractionType(x, t_bool, ty)
    ctx = ctx.with_var(name, ty)
    for x in xs:
        ctx = ctx.with_var(x, t_bool)
        term = Application(term, Var(x))
    assert _selfification_liquid(ctx, term) is None
    with pytest.raises(RuntimeError), exact_application_identities():
        encoded = _selfification_liquid(ctx, term)
        assert isinstance(encoded, LiquidApp)
        assert set(xs) <= set(liquid_free_vars(encoded))
        raise RuntimeError("leave exact mode")
    assert _selfification_liquid(ctx, term) is None


@pytest.mark.parametrize("arity", [31, 32, 40])
def test_wide_function_properties_retain_their_call_equations(arity):
    params = " ".join(f"(x{i}:Bool)" for i in range(arity))
    args = " ".join(f"x{i}" for i in range(arity))
    driver = parse(f"@bounded_cnf(1) def f {params}:Bool := ?h; @property(1) def law {params}:Bool := f {args} = x0;")
    completed = fill(driver, solve(driver, BooleanBoundedSynthesizer(), budget=10))
    for first in (False, True):
        assert call(driver, completed, "f", first, *([not first] * (arity - 1))) is first


def test_published_lut7_is_feasible_at_five_clauses():
    case = next(c for c in json.loads((ROOT / "manifest.json").read_text())["cases"] if c["id"] == "lut7-ctrl_7_1")
    circuit = load_case(case)
    # Independent five-clause certificate over the original Verilog ports.
    certificate = {"i_32": [[30, -31], [-30, 31], [29, 31], [28, 31], [27, 28, 29]]}
    assert check(circuit, certificate, 5)["status"] == "verified_solved"
    driver = parse((ROOT / case["aeon"]).read_text())
    # This is a correctness regression, not a 15-second performance gate on CI.
    # Deadline enforcement is exercised separately with injected blocking calls.
    completed = fill(driver, solve(driver, BooleanBoundedSynthesizer(), budget=60))
    assert check(circuit, extract(completed, circuit, 5), 5)["status"] == "verified_solved"
