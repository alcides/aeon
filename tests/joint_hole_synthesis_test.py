"""Whole-program candidates must be complete and valid before fitness runs."""

from pathlib import Path

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Hole, Literal, Var
from aeon.core.types import t_bool, t_float, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.evaluation_pool import EvaluationPool, INVALID
from aeon.synthesis.fitness_eval import make_bundled_fitness_evaluator, require_complete_program, set_program_tail
from aeon.synthesis.identification import incomplete_functions_and_holes, term_has_holes
from aeon.synthesis.joint import JointCandidate, JointSynthesizer
from aeon.synthesis.modules.genetic_programming import GeneticProgrammingSynthesizer
from aeon.synthesis.modules.random_search import RandomSearchSynthesizer
from aeon.synthesis.pbt.runner import property_corpora_for_targets
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


def parse(source):
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=True))
    assert not driver.parse(aeon_code=source)
    return driver


def solve(driver, backend, budget=0.1):
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


def fill(driver, mapping):
    program = driver.core
    for name, value in mapping.items():
        assert value is not None
        program = substitution(program, value, name)
    assert not term_has_holes(program)
    return program


def test_product_retains_each_holes_type_scope_and_validates_together():
    driver = parse("""
    def n : {v:Int | v >= 1} := ?hn;
    def weight : Float := ?hw;
    def choose (x:Int) : Int := if ?hc then ?ht else ?he;
    def score (a:Int) (b:Float) (c:Int) : Float := native "float(a) + b + float(c)";
    @minimize_float(score n weight (choose 3))
    def cost : Float := score n weight (choose 3);
    """)
    before = repr(driver.metadata)

    class Inspect(JointSynthesizer):
        def synthesize_joint(self, holes, validate, evaluate, fun_name, metadata, budget, ui):
            assert [h.name.name for h in holes] == ["hn", "hw", "hc", "ht", "he"]
            assert "x" not in {n.name for n, _ in holes[0].ctx.vars()}
            x = next(n for n, _ in holes[3].ctx.vars() if n.name == "x")
            good = JointCandidate(
                (Literal(2, t_int), Literal(0.5, t_float), Literal(True, t_bool), Var(x), Literal(0, t_int))
            )
            assert not validate(JointCandidate(good.terms[:-1]))
            assert not validate(JointCandidate((Hole(Name("unfilled", 0)), *good.terms[1:])))
            assert not validate(JointCandidate((Literal(0, t_int), *good.terms[1:])))
            assert not validate(JointCandidate((Literal(2.0, t_float), *good.terms[1:])))
            with pytest.raises(InvalidIndividualException):
                evaluate(JointCandidate(good.terms[:-1]))
            assert validate(good)
            assert evaluate(good) == [5.5]
            return good

    mapping = solve(driver, Inspect())
    assert len(mapping) == 5
    completed = fill(driver, mapping)
    cost = next(n for n, _ in incomplete_functions_and_holes(driver.typing_ctx, driver.core) if n.name == "n")
    assert aeon_eval(set_program_tail(completed, Var(cost)), driver.evaluation_ctx) == 2
    assert repr(driver.metadata) == before


@pytest.mark.parametrize("backend", [RandomSearchSynthesizer, GeneticProgrammingSynthesizer])
def test_actual_backends_fill_multiple_holes_in_one_function(backend):
    driver = parse("""
    def f (x:Int) : Int := if ?cond then ?left else ?right;
    """)
    mapping = solve(driver, backend(seed=0))
    assert {name.name for name in mapping} == {"cond", "left", "right"}
    fill(driver, mapping)


@pytest.mark.parametrize("backend", [RandomSearchSynthesizer, GeneticProgrammingSynthesizer])
def test_actual_backends_evaluate_coupled_mixed_type_holes(backend):
    driver = parse("""
    def x : Int := ?hx;
    def y : Float := ?hy;
    def metric (a:Int) (b:Float) : Float := native "float(a*a) + b*b";
    @minimize_float(metric x y)
    def cost : Float := metric x y;
    """)
    mapping = solve(driver, backend(seed=0))
    assert len(mapping) == 2
    fill(driver, mapping)


def test_joint_search_selects_relational_properties_once():
    driver = parse("""
    def f (x:Int) : Bool := ?hf;
    def g (x:Int) : Bool := ?hg;
    @property(4)
    def relational (x:Int) : Bool := f x = g x;
    """)
    targets = {name for name, _ in incomplete_functions_and_holes(driver.typing_ctx, driver.core)}
    corpora = property_corpora_for_targets(driver.typing_ctx, driver.core, driver.metadata, targets, targets)
    assert len(corpora) == 1

    class Inspect(JointSynthesizer):
        def synthesize_joint(self, holes, validate, evaluate, fun_name, metadata, budget, ui):
            assert len(metadata[fun_name]["goals"]) == 1
            unequal = JointCandidate((Literal(True, t_bool), Literal(False, t_bool)))
            equal = JointCandidate((Literal(True, t_bool), Literal(True, t_bool)))
            assert validate(unequal) and validate(equal)
            assert evaluate(unequal) == [4.0]
            assert evaluate(equal) == [0.0]
            return equal

    fill(driver, solve(driver, Inspect()))


def test_final_gate_rejects_partial_backend_result():
    driver = parse("def x:Int := ?hx; def y:Float := ?hy;")

    class Incomplete(JointSynthesizer):
        def synthesize_joint(self, *args):
            return JointCandidate((Literal(0, t_int),))

    mapping = solve(driver, Incomplete())
    assert len(mapping) == 2 and all(value is None for value in mapping.values())


def test_pool_rejects_open_program_without_executing_any_computation():
    def must_not_execute(program):
        raise AssertionError("fitness executed on an open program")

    pool = EvaluationPool(lambda candidate: candidate, {"fitness": must_not_execute})
    try:
        assert pool.run(Hole(Name("open", 1)))["fitness"] == (INVALID, None)
    finally:
        pool.close()


def test_bundled_fitness_defers_unfilled_prefix_and_scores_actual_values():
    driver = parse("""
    def x : Int := ?hx;
    @minimize_int(x + y)
    def y : Int := ?hy;
    """)
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    anchor = targets[1][0]
    goals = driver.metadata[anchor]["goals"]
    fitness = make_bundled_fitness_evaluator(goals, driver.evaluation_ctx, anchor, driver.core)
    with pytest.raises(InvalidIndividualException):
        fitness(driver.core)
    for a, b in [(2, 3), (7, 11)]:
        completed = fill(driver, {targets[0][1][0]: Literal(a, t_int), targets[1][1][0]: Literal(b, t_int)})
        assert fitness(completed) == [float(a + b)]


def test_named_main_hole_is_not_an_entrypoint_placeholder():
    driver = parse("def x:Int := ?main;")
    with pytest.raises(InvalidIndividualException):
        require_complete_program(driver.core)


@pytest.mark.parametrize("backend", [RandomSearchSynthesizer, GeneticProgrammingSynthesizer])
@pytest.mark.parametrize("filename", ["float_quadratic", "int_booth", "int_constrained", "int_sphere"])
def test_previous_coupled_hole_crashes_have_complete_candidate_fitness(filename, backend):
    path = Path(__file__).resolve().parents[1] / f"examples/synthesis/ortools/{filename}.ae"
    driver = parse(path.read_text())
    mapping = solve(driver, backend(seed=0), budget=0.2)
    assert len(mapping) == (3 if filename == "int_sphere" else 2)
    # A search can exhaust its budget; any reported result is atomic.
    assert all(v is None for v in mapping.values()) or all(v is not None for v in mapping.values())
    if any(v is not None for v in mapping.values()):
        fill(driver, mapping)


@pytest.mark.parametrize("backend", [RandomSearchSynthesizer, GeneticProgrammingSynthesizer])
def test_pade_native_fitness_receives_all_three_coefficients(backend, monkeypatch):
    from aeon.synthesis.modules import genetic_programming as gp, random_search
    from aeon.synthesis.uis.api import SynthesisUI

    path = Path(__file__).resolve().parents[1] / "examples/synthesis/autonumerics/exp2_pade.ae"
    driver = parse(path.read_text())
    values = (1.5625291599338442, -0.2910765369491663, -1.4427239805682266)
    if backend is RandomSearchSynthesizer:
        by_function = dict(zip(("pa", "pb", "pc"), values))
        monkeypatch.setattr(
            random_search,
            "iter_random_candidates",
            lambda ctx, target, function, *args: iter([Literal(by_function[function.name], t_float)]),
        )
    else:
        from itertools import cycle

        coefficients = cycle(values)
        monkeypatch.setattr(gp, "map_genome", lambda *args, **kwargs: Literal(next(coefficients), t_float))

    observed = []

    class UI(SynthesisUI):
        def register_front(self, front, elapsed_time):
            observed.extend(score for score, candidate in front)

    mapping = synthesize_holes(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        incomplete_functions_and_holes(driver.typing_ctx, driver.core),
        driver.metadata,
        backend(),
        0,
        UI(),
    )
    fill(driver, mapping)
    assert [mapping[h].value for h in mapping] == list(values)
    assert observed and len(observed[0]) == 1
    assert 0 < observed[0][0] < 0.002
