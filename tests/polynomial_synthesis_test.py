"""Polynomial certificates prove universal contracts, not just sampled examples."""

import time

import pytest
import z3

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import t_int
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import iterate_top_level
from aeon.synthesis.modules.polynomial import CertificateProblem, PolynomialConfig, PolynomialSynthesizer
from aeon.synthesis.modules.synthesizerfactory import SynthesizerFamily, make_synthesizer, synthesizer_family
from aeon.synthesis.solver_problem import SolverClause, SolverHole, SolverProblem
from aeon.utils.name import Name
from tests.joint_hole_synthesis_test import fill, parse, solve


def evaluate_function(driver, completed, function, *inputs):
    name = next(d.var_name for d in iterate_top_level(completed) if d.var_name.name == function)
    term = Var(name)
    for value in inputs:
        term = Application(term, Literal(value, t_int))
    return aeon_eval(set_program_tail(completed, term), driver.evaluation_ctx)


def test_registered_for_cli_and_ide():
    from aeon.lsp.server import SYNTHESIZERS

    assert isinstance(make_synthesizer("polynomial"), PolynomialSynthesizer)
    assert "polynomial" in SYNTHESIZERS
    assert synthesizer_family("polynomial") == SynthesizerFamily.CONSTRAINT_SOLVING


def test_quadratic_template_is_synthesized_and_executes_beyond_examples():
    driver = parse("def f(x:Int):{v:Int | v = x*x + 3*x + 7} := ?hf;")
    completed = fill(driver, solve(driver, PolynomialSynthesizer(), budget=10))
    for x in (-1000, -3, 0, 2, 1000):
        assert evaluate_function(driver, completed, "f", x) == x * x + 3 * x + 7


def test_single_hole_uses_whole_program_relational_property():
    driver = parse("def f(x:Int):Int := ?hf; @property(4) def related(x:Int):Bool := f x = x*x + 11;")
    completed = fill(driver, solve(driver, PolynomialSynthesizer(), budget=10))
    assert evaluate_function(driver, completed, "f", 1234) == 1234**2 + 11


def test_joint_holes_share_coefficients_and_dependent_contracts():
    driver = parse("def f(x:Int):{v:Int | v = x*x + 1} := ?hf; def g(x:Int):{v:Int | v = f x + x} := ?hg;")
    completed = fill(driver, solve(driver, PolynomialSynthesizer(), budget=10))
    assert evaluate_function(driver, completed, "f", 17) == 290
    assert evaluate_function(driver, completed, "g", 17) == 307


def test_constant_coefficients_in_user_supplied_program_sketch():
    driver = parse("def a:Int := ?ha; def b:Int := ?hb; @property(4) def correct(x:Int):Bool := a*x*x + b = 3*x*x + 7;")
    completed = fill(driver, solve(driver, PolynomialSynthesizer(), budget=10))
    assert evaluate_function(driver, completed, "a") == 3
    assert evaluate_function(driver, completed, "b") == 7


def app(op, *args):
    return LiquidApp(Name(op, 0), list(args))


def certificate_for(premise, conclusion, config=PolynomialConfig(), variables=None):
    x = Name("x", 1)
    problem = SolverProblem((), (SolverClause(variables or ((x, t_int),), premise, conclusion),))
    encoded = CertificateProblem(problem, config, time.monotonic() + 10)
    encoded.build()
    encoded.solver.set(timeout=10000)
    return encoded


def test_handelman_products_are_needed_for_interval_polynomial():
    x = LiquidVar(Name("x", 1))
    one, zero = LiquidLiteralInt(1), LiquidLiteralInt(0)
    premise = app("&&", app(">=", x, zero), app("<=", x, one))
    conclusion = app(">=", app("*", x, app("-", one, x)), zero)
    assert (
        certificate_for(premise, conclusion, PolynomialConfig(certificate_degree=1, sos_degree=0)).solver.check()
        == z3.unsat
    )
    assert (
        certificate_for(premise, conclusion, PolynomialConfig(certificate_degree=2, sos_degree=0)).solver.check()
        == z3.sat
    )


def test_sum_of_squares_proves_global_nonnegativity_without_domain_bounds():
    x = LiquidVar(Name("x", 1))
    conclusion = app(">=", app("*", x, x), LiquidLiteralInt(0))
    assert (
        certificate_for(LiquidLiteralBool(True), conclusion, PolynomialConfig(sos_degree=0)).solver.check() == z3.unsat
    )
    assert certificate_for(LiquidLiteralBool(True), conclusion).solver.check() == z3.sat


def test_equality_assumptions_have_unrestricted_polynomial_multipliers():
    x = LiquidVar(Name("x", 1))
    premise = app("==", app("*", x, x), LiquidLiteralInt(1))
    conclusion = app("==", app("*", app("*", x, x), app("*", x, x)), LiquidLiteralInt(1))
    assert certificate_for(premise, conclusion).solver.check() == z3.sat


def test_certificate_solver_receives_no_quantifiers_or_universal_input_symbols():
    x = LiquidVar(Name("x", 1))
    encoded = certificate_for(LiquidLiteralBool(True), app(">=", app("*", x, x), LiquidLiteralInt(0)))
    from z3.z3util import get_vars

    def walk(term):
        assert not z3.is_quantifier(term)
        for child in term.children():
            walk(child)

    for constraint in encoded.solver.assertions():
        walk(constraint)
        assert all(str(v).startswith("polynomial_c") for v in get_vars(constraint))


@pytest.mark.parametrize("comparison", [">", "<"])
def test_strict_conclusions_do_not_accept_zero(comparison):
    x = LiquidVar(Name("x", 1))
    assert (
        certificate_for(LiquidLiteralBool(True), app(comparison, app("-", x, x), LiquidLiteralInt(0))).solver.check()
        == z3.unsat
    )


def test_disjunctive_and_negated_premises_cover_every_branch():
    x = LiquidVar(Name("x", 1))
    premise = app("||", app("<", x, LiquidLiteralInt(-1)), app(">", x, LiquidLiteralInt(1)))
    assert certificate_for(premise, app(">=", app("*", x, x), LiquidLiteralInt(1))).solver.check() == z3.sat
    assert (
        certificate_for(app("!", app("==", x, LiquidLiteralInt(0))), app(">=", x, LiquidLiteralInt(0))).solver.check()
        == z3.unsat
    )


def test_impossible_contract_fails_without_claiming_unrealizability():
    driver = parse("def f(x:Int):{v:Int | v = x*x*x} := ?hf;")
    with pytest.raises(SynthesisNotSuccessful, match="configured degrees"):
        solve(driver, PolynomialSynthesizer(PolynomialConfig(degree=2)), budget=10)
    completed = fill(driver, solve(driver, PolynomialSynthesizer(PolynomialConfig(degree=3)), budget=10))
    assert evaluate_function(driver, completed, "f", -5) == -125


@pytest.mark.parametrize(
    "source",
    [
        "def f(x:Int):{v:Int | v = x / 2} := ?hf;",
        "def f(x:Int):{v:Int | v = x % 2} := ?hf;",
        "def f(x:Int):Bool := ?hf;",
        "def f(x:Float):Int := ?hf;",
    ],
)
def test_unsupported_semantics_are_rejected(source):
    with pytest.raises(UnsupportedSynthesisGoal, match="Polynomial"):
        solve(parse(source), PolynomialSynthesizer(), budget=1)


def test_real_coefficient_template():
    driver = parse("def f(x:Float):{v:Float | v = 0.5*x*x + 0.25} := ?hf;")
    completed = fill(driver, solve(driver, PolynomialSynthesizer(), budget=10))
    name = next(d.var_name for d in iterate_top_level(completed) if d.var_name.name == "f")
    from aeon.core.types import t_float

    term = Application(Var(name), Literal(4.0, t_float))
    assert aeon_eval(set_program_tail(completed, term), driver.evaluation_ctx) == 8.25


def test_failed_validation_never_reaches_objectives(monkeypatch):
    from aeon.synthesis.modules import polynomial

    monkeypatch.setattr(polynomial, "solve_polynomial", lambda *args: object())

    def must_not_run(candidate):
        raise AssertionError("Invalid candidate reached fitness")

    joint = Name("joint", 0)
    with pytest.raises(SynthesisNotSuccessful, match="failed validation"):
        PolynomialSynthesizer().synthesize_joint(
            (), lambda c: False, must_not_run, joint, {joint: {"solver_problem": None, "goals": [1]}}
        )


def test_budget_and_size_limits():
    problem = SolverProblem((SolverHole(Name("h", 1), Name("sym", 2), (), (), t_int),), ())
    with pytest.raises(SynthesisNotSuccessful, match="time budget"):
        CertificateProblem(problem, PolynomialConfig(), time.monotonic() - 1)
    with pytest.raises(SynthesisNotSuccessful, match="unknown-coefficient limit"):
        certificate_for(LiquidLiteralBool(True), LiquidLiteralBool(False), PolynomialConfig(max_unknowns=1))
    with pytest.raises(SynthesisNotSuccessful, match="monomial limit"):
        CertificateProblem(problem, PolynomialConfig(max_terms=1), time.monotonic() + 1).sos(2)


def test_configuration_errors_are_controlled(monkeypatch):
    monkeypatch.setenv("AEON_POLYNOMIAL_DEGREE", "invalid")
    with pytest.raises(UnsupportedSynthesisGoal, match="integers"):
        PolynomialSynthesizer()
    with pytest.raises(UnsupportedSynthesisGoal, match="nonnegative"):
        PolynomialConfig(degree=-1)
