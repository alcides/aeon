"""Size fitness measures hole replacements and participates in candidate selection."""

import subprocess
import sys
from pathlib import Path

import pytest

from aeon.core.substitutions import substitution
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import Kind, t_bool, t_int
from aeon.errors import InvalidDecoratorArgumentError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import InvalidIndividualException, UnsupportedSynthesisGoal
from aeon.synthesis.decorators import Goal
from aeon.synthesis.entrypoint import make_evaluators, synthesize_holes
from aeon.synthesis.expression_size import expression_size, make_size_evaluator
from aeon.synthesis.fitness_eval import make_bundled_fitness_evaluator
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.joint import JointCandidate, JointSynthesizer
from aeon.synthesis.modules import enumerative, genetic_programming, random_search
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.scope import fitness_relevant_names
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


def parse(source):
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, no_main=True))
    assert not driver.parse(aeon_code=source)
    return driver


def solve(driver, backend, budget=1):
    return synthesize_holes(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        incomplete_functions_and_holes(driver.typing_ctx, driver.core),
        driver.metadata,
        backend,
        budget,
        SilentSynthesisUI(),
    )


X = Name("x", 10)
ONE = Literal(1, t_int)


@pytest.mark.parametrize(
    "term, expected",
    [
        (ONE, 1),
        (Var(X), 1),
        (Application(Var(X), ONE), 3),
        (Abstraction(X, ONE), 2),
        (If(Literal(True, t_bool), ONE, ONE), 4),
        (Let(X, ONE, Var(X)), 3),
        (Rec(X, t_int, ONE, Var(X), decreasing_by=(ONE,)), 3),
        (Annotation(ONE, t_int), 2),
        (TypeApplication(Var(X), t_int), 2),
        (TypeAbstraction(X, Kind.BASE, ONE), 2),
        (RefinementAbstraction(X, t_int, ONE), 2),
        (RefinementApplication(Var(X), Abstraction(X, Literal(True, t_bool))), 4),
    ],
)
def test_core_node_metric(term, expected):
    assert expression_size(term) == expected


def test_unresolved_replacement_has_no_size_fitness():
    with pytest.raises(InvalidIndividualException):
        expression_size(Hole(Name("h", 1)))


def test_registers_static_goal_without_hiding_target_or_generating_helper():
    driver = parse("@allow_recursion @minimize_size def f(x:Int):Int := ?h;")
    function, _ = incomplete_functions_and_holes(driver.typing_ctx, driver.core)[0]
    assert driver.metadata[function]["goals"] == [Goal(True, 1, function, "size")]
    assert fitness_relevant_names(driver.metadata) == set()
    assert isinstance(driver.core.body, Literal)


def test_size_rejects_arguments_instead_of_silently_ignoring_them():
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 1, no_main=True))
    errors = driver.parse(aeon_code="@minimize_size(42) def f:Int := ?h;")
    assert any(isinstance(error, InvalidDecoratorArgumentError) for error in errors)


def test_explicit_tactics_cannot_bypass_size_capability_check():
    driver = parse("@minimize_size def f:Int := by choose_literal;")
    with pytest.raises(UnsupportedSynthesisGoal, match="explicit tactic"):
        solve(driver, make_synthesizer("enumerative"))


def test_documented_double_example():
    source = Path(__file__).resolve().parents[1] / "examples/synthesis/minimize_size.ae"
    driver = parse(source.read_text())
    # The refinement solver can generate the first valid literal immediately.
    result = solve(driver, make_synthesizer("enumerative"), budget=0)
    assert list(result.values()) == [Literal(2, t_int)]


@pytest.mark.parametrize(
    "definition, replacement, expected",
    [
        ("def f(x:Int):Int := x * (?h:Int) + 100;", ONE, 1),
        ("def f(x:Int):Int := ?h;", ONE, 1),
        ("def f:(x:Int) -> Int := ?h;", Abstraction(X, Var(X)), 2),
    ],
)
def test_measures_only_inserted_expression(definition, replacement, expected):
    driver = parse("@minimize_size " + definition)
    function, holes = incomplete_functions_and_holes(driver.typing_ctx, driver.core)[0]
    evaluator = make_size_evaluator(driver.core, function)
    assert evaluator(substitution(driver.core, replacement, holes[0])) == [expected]


def test_size_only_fitness_never_executes_prefix_or_candidate(monkeypatch):
    from aeon.synthesis import fitness_eval

    driver = parse("def prefix:Int := 1; @minimize_size def f(x:Int):Int := ?h;")
    function, holes = incomplete_functions_and_holes(driver.typing_ctx, driver.core)[0]

    def must_not_evaluate(*args):
        raise AssertionError("static size scoring must not execute user code")

    monkeypatch.setattr(fitness_eval, "aeon_eval", must_not_evaluate)
    fitness = make_bundled_fitness_evaluator(
        driver.metadata[function]["goals"], driver.evaluation_ctx, function, driver.core
    )
    # This application could not be evaluated, but its static size is defined.
    replacement = Application(Var(Name("undefined", 1000)), ONE)
    assert fitness(substitution(driver.core, replacement, holes[0])) == [3.0]


def test_composes_with_numeric_resource_and_property_goals_in_order(monkeypatch):
    from aeon.synthesis import entrypoint, fitness_eval

    driver = parse("""
        @minimize_int(f 3)
        @minimize_size
        @minimize_cputime(f 3)
        @minimize_energy(f 3)
        def f(x:Int):Int := ?h;
    """)
    function, holes = incomplete_functions_and_holes(driver.typing_ctx, driver.core)[0]
    goals = driver.metadata[function]["goals"]
    goals.append(Goal(True, 1, Name("property", 0), "property"))
    properties = [lambda program: 7.0]
    for module in (entrypoint, fitness_eval):
        monkeypatch.setattr(module, "measure_cputime", lambda thunk: float(thunk()) / 10)
        monkeypatch.setattr(module, "measure_energy", lambda thunk: float(thunk()) / 5)
    filled = substitution(driver.core, ONE, holes[0])
    expected = [1.0, 1.0, 0.1, 0.2, 7.0]
    bundled = make_bundled_fitness_evaluator(goals, driver.evaluation_ctx, function, driver.core, properties)
    separate = make_evaluators(driver.evaluation_ctx, function, driver.metadata, properties, driver.core)
    assert bundled(filled) == expected
    assert [score for evaluator in separate for score in evaluator(filled)] == expected


def test_joint_size_sums_each_owners_holes_and_keeps_property_objective():
    driver = parse("""
        @minimize_size
        def f(x:Int):Int := if ?condition then ?left else ?right;
        @minimize_size
        def g:Int := ?other;
        @property(4)
        def same(x:Int):Bool := f x = g;
    """)

    class Inspect(JointSynthesizer):
        supports_size_objective = True

        def synthesize_joint(self, holes, validate, evaluate, fun_name, metadata, budget, ui):
            assert [hole.name.name for hole in holes] == ["condition", "left", "right", "other"]
            candidate = JointCandidate((Literal(True, t_bool), ONE, If(Literal(True, t_bool), ONE, ONE), ONE))
            assert validate(candidate)
            assert evaluate(candidate) == [6.0, 1.0, 0.0]
            return candidate

    assert len(solve(driver, Inspect())) == 4


@pytest.mark.parametrize("backend", ["enumerative", "random_search", "gp"])
def test_real_search_prefers_smaller_valid_expression(monkeypatch, backend):
    driver = parse("@minimize_size def f:{v:Int | v = 1} := ?h;")
    large = If(Literal(True, t_bool), ONE, ONE)
    # The smallest invalid term must not win; the smaller valid term must beat
    # an earlier, larger term. Patch generation only, retaining validation,
    # worker fitness and the backend's actual Pareto selection.
    candidates = [large, Literal(0, t_int), ONE]
    monkeypatch.setattr(enumerative, "iter_candidates", lambda *args, **kwargs: iter(candidates))
    monkeypatch.setattr(random_search, "iter_random_candidates", lambda *args, **kwargs: iter(candidates))
    if backend == "gp":
        from itertools import chain, repeat

        stream = chain(candidates, repeat(ONE))
        monkeypatch.setattr(genetic_programming, "map_genome", lambda *args, **kwargs: next(stream))
        # Deterministic termination after several assessments, independent of CI speed.
        ticks = chain(range(30), repeat(10000))
        monkeypatch.setattr(genetic_programming, "monotonic", lambda: next(ticks) / 100)
    result = solve(driver, make_synthesizer(backend), budget=10)
    assert list(result.values()) == [ONE]


@pytest.mark.parametrize("backend", ["tdsyn_enumerative", "tdsyn_random"])
def test_type_directed_search_scores_size(backend):
    driver = parse("@minimize_size def f:{v:Int | v = 1} := ?h;")
    result = solve(driver, make_synthesizer(backend), budget=0.5)
    assert list(result.values()) == [ONE]


@pytest.mark.parametrize("backend", ["backward_lit", "forward_close", "dp_gp"])
def test_backends_without_size_optimization_reject_goal(backend):
    driver = parse("@minimize_size def f:Int := ?h;")
    with pytest.raises(UnsupportedSynthesisGoal, match="@minimize_size"):
        solve(driver, make_synthesizer(backend))


def test_cli_reports_unsupported_size_objective_without_traceback(tmp_path):
    source = tmp_path / "size.ae"
    source.write_text("@minimize_size def f:Int := ?h;")
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "backward_lit", str(source)],
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 2
    assert "@minimize_size" in result.stderr
    assert "Traceback" not in result.stderr
