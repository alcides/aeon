"""Transformation obligations, counterexample feedback and emitted algorithms."""

from dataclasses import replace
from pathlib import Path
from itertools import product
from time import monotonic

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.compilation.session import CompilationSession
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import t_int
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import iterate_top_level
from aeon.synthesis.modules.dp_gp import DPSynthesizer
from aeon.synthesis.modules.dp_gp.checking import (
    key_counterexample,
    relation_counterexample,
    representation_counterexample,
    state_requirements,
)
from aeon.synthesis.modules.dp_gp.emission import UPDATES
from aeon.synthesis.modules.dp_gp.expressions import Expr, extract, literal, variable
from aeon.synthesis.modules.dp_gp.model import Config, Meter, Node, Plan, Problem, execute, optimum, thin, trace
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer, synthesizer_family, SynthesizerFamily
from aeon.utils.name import Name
from tests.joint_hole_synthesis_test import parse, solve, fill


ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture(autouse=True)
def session():
    with CompilationSession().activate():
        yield


def problem():
    x, y, z, a = [variable(i) for i in range(4)]
    return Problem(
        (x, y, literal(0)),
        literal(True),
        (Expr("-", (x, literal(1))), y, Expr("+", (z, a))),
        (Expr("*", (a, y)), a, literal(1)),
        x,
        (0, 0, 0),
        0,
        (3, 2),
    )


def meter():
    return Meter(monotonic() + 60, 100000)


def test_preorder_rejects_current_value_only_and_accepts_all_extensions():
    p = problem()
    assert relation_counterexample(p, (2, 0, 0), monotonic() + 10) is None
    assert relation_counterexample(p, (0, 2, 0), monotonic() + 10) is not None
    assert relation_counterexample(p, (3, 0, 0), monotonic() + 10) is not None
    # Non-monotone objectives cannot be justified by a few positive samples.
    p = replace(p, score=Expr("*", (variable(0), variable(0))))
    assert relation_counterexample(p, (2, 0, 0), monotonic() + 10) is not None


def test_thinning_preserves_one_equivalent_representative():
    assert thin([(1, 2, 3)] * 5, (1, 1, 1)) == ((1, 2, 3),)
    assert len(thin([(1, 2, 3), (1, 4, 5)], (2, 0, 0))) == 1
    assert thin([], (2, 0, 0)) == ()


def test_representation_requires_queries_and_incremental_commutation():
    p = problem()
    plan = Plan(relation=(2, 0, 0), solution_fields=(0,), updates=(UPDATES[4],))
    assert representation_counterexample(p, plan, monotonic() + 10) is None
    assert representation_counterexample(p, replace(plan, solution_fields=(1,)), monotonic() + 10)
    failure = representation_counterexample(p, replace(plan, updates=(UPDATES[0],)), monotonic() + 10)
    assert failure[0] == "update"
    x, y = failure[2]
    assert UPDATES[0].run((x, y)) != x + y


def test_memoization_checks_frontiers_and_keeps_stages_separate():
    p = problem()
    a = Node(0, (1, 0, 0), ((0, 0, 0),), ())
    b = Node(1, (1, 0, 0), (), ())
    root = Node(2, (0, 0, 0), (), ((0, a), (1, b)))
    plan = Plan(relation=(2, 0, 0), solution_fields=(0,), key_fields=())
    # Equal projected states at distinct remaining depths never collide.
    assert key_counterexample([root], p, plan, meter()) is None
    root = trace(p, (3, 2), meter())
    assert key_counterexample([root], p, plan, meter()) is None
    # Within one context, different remaining gains must not share a key.
    p = replace(p, step=(p.step[0], variable(3), p.step[2]))
    root = trace(p, (3, 2), meter())
    assert key_counterexample([root], p, plan, meter()) is not None
    assert key_counterexample([root], p, replace(plan, key_fields=(1,)), meter()) is None


def test_state_projection_cannot_drop_transition_or_key_dependencies():
    p = problem()
    plan = Plan(solution_fields=(0,), key_fields=(1,), state_fields=(1,))
    assert state_requirements(p, plan) == {1}
    p = replace(p, allow=Expr("==", (variable(2), literal(0))))
    assert 2 in state_requirements(p, plan)


@pytest.mark.parametrize("inputs", [(0, 0), (0, 2), (1, 0), (3, 2)])
def test_reference_and_stages_preserve_optima_with_deterministic_costs(inputs):
    p = problem()
    root = trace(p, inputs, meter())
    plan = Plan(relation=(2, 0, 0), solution_fields=(0,), updates=(UPDATES[4],), key_fields=(1,), state_fields=(1,))
    full, cost = execute(p, root, plan)
    reference, old = execute(p, root)
    assert optimum(p, full) == optimum(p, reference) == inputs[0] * inputs[1]
    assert cost.retained <= old.retained
    assert cost.solution_cells < old.solution_cells
    assert cost.state_cells < old.state_cells


@pytest.mark.parametrize("name", ["native", "print", "uninterpreted"])
def test_effectful_or_opaque_components_are_rejected(name):
    with pytest.raises(UnsupportedSynthesisGoal):
        extract(Application(Var(Name(name, 0)), Literal(1, t_int)), {})


def test_recursive_components_and_limits_are_explicit():
    name = Name("loop", 999)
    with pytest.raises(UnsupportedSynthesisGoal):
        extract(Var(name), {name: Var(name)})
    with pytest.raises(UnsupportedSynthesisGoal):
        Config(proposals=0)
    with pytest.raises(SynthesisNotSuccessful):
        trace(problem(), (3, 2), Meter(monotonic() + 1, 1))


def test_factory_seed_and_family(monkeypatch):
    monkeypatch.setenv("AEON_SEED", "17")
    backend = make_synthesizer("dp_gp")
    assert isinstance(backend, DPSynthesizer)
    assert backend.seed == 17
    assert synthesizer_family("dp_gp") == SynthesizerFamily.METAHEURISTIC


@pytest.mark.parametrize("case", ["knapsack", "path"])
def test_real_compiler_gp_components_reference_and_held_out_inputs(case):
    driver = parse((ROOT / f"examples/synthesis/dp_gp/{case}.ae").read_text())
    before = repr(driver.metadata)
    backend = DPSynthesizer(config=Config(proposals=160))
    completed = fill(driver, solve(driver, backend, budget=60))
    report = backend.last_report
    assert report["stop_reason"] == "completed"
    assert len(report["stages"]) == 4
    assert all(s["generations"] > 0 for s in report["stages"])
    assert report["plan"]["relation"] == (2, 0, 0)
    assert report["plan"]["solution_fields"] == (0,)
    assert len(report["plan"]["state_fields"]) < 3
    assert set(report["held_out_indices"]).isdisjoint(report["training_indices"])
    assert set(report["held_out_indices"]).isdisjoint(report["checking_indices"])
    assert repr(driver.metadata) == before
    functions = {d.var_name.name: d.var_name for d in iterate_top_level(completed)}
    for i in report["held_out_indices"]:
        values = report["instances"][i]
        results = []
        for name in ("reference", "optimized"):
            call = Var(functions[name])
            for value in values:
                call = Application(call, Literal(value, t_int))
            results.append(aeon_eval(set_program_tail(completed, call), driver.evaluation_ctx))
        assert results[0] == results[1]
        if case == "knapsack":
            n, capacity = values
            items = [(0, 1) if j <= 1 else (2, 3) if j <= 3 else (3, 4) for j in range(1, n + 1)]
            expected = max(
                sum(v * b for (_, v), b in zip(items, bits))
                for bits in product((0, 1), repeat=n)
                if sum(w * b for (w, _), b in zip(items, bits)) <= capacity
            )
            assert results[1] == expected
    assert sum(r["full"]["solution_cells"] for r in report["ablations"]) < sum(
        r["thinning"]["solution_cells"] for r in report["ablations"]
    )
    assert sum(r["full"]["calls"] for r in report["ablations"]) < sum(
        r["reference"]["calls"] for r in report["ablations"]
    )


def test_missing_opt_in_and_zero_budget_are_controlled_failures():
    with pytest.raises(UnsupportedSynthesisGoal):
        solve(parse("def f(x:Int):Int := ?h;"), DPSynthesizer())
    driver = parse((ROOT / "examples/synthesis/dp_gp/knapsack.ae").read_text())
    with pytest.raises(SynthesisNotSuccessful):
        solve(driver, DPSynthesizer(), budget=0)


def test_shared_imported_datatypes_have_one_handler_per_constructor():
    # DP has a diamond of shared datatype imports. Before deduplication,
    # lowering supplied multiple copies of the same eliminator handlers.
    driver = parse("import DP; def value:Int := DP.get (DP.vector 3 7 9) 1;")
    name = next(d.var_name for d in iterate_top_level(driver.core) if d.var_name.name == "value")
    assert aeon_eval(set_program_tail(driver.core, Var(name)), driver.evaluation_ctx) == 7


def test_gp_changes_components_when_the_reference_objective_changes():
    source = (
        (ROOT / "examples/synthesis/dp_gp/knapsack.ae")
        .read_text()
        .replace("def objective(v:Int)(w:Int)(k:Int):Int := v;", "def objective(v:Int)(w:Int)(k:Int):Int := w;")
    )
    backend = DPSynthesizer(config=Config(proposals=160))
    solve(parse(source), backend, budget=60)
    assert backend.last_report["plan"]["relation"] == (0, 2, 0)
    assert backend.last_report["plan"]["solution_fields"] == (1,)


def test_counterexample_restarts_gp_and_invalidates_previous_fitness(monkeypatch):
    from aeon.synthesis.modules.genetic_programming import GeneticProgrammingSynthesizer

    original = GeneticProgrammingSynthesizer.search_components

    def controlled(self, initial, decode, validate, evaluate, budget, max_assessments=1000):
        # First representation epoch sees only update(old, delta) = old,
        # which fits initial delta=0 cases. SMT must produce a nonzero delta.
        if self.seed in (101, 102):
            bad = decode([1, 0], 1)
            assert validate(bad)
            score = evaluate(bad)[0]
            assert (score < 1) == (self.seed == 101)
            if self.seed == 102:
                good = decode([1, 4], 1)
                assert validate(good) and evaluate(good)[0] < 1
                return good
            return bad
        return original(self, initial, decode, validate, evaluate, budget, max_assessments)

    monkeypatch.setattr(GeneticProgrammingSynthesizer, "search_components", controlled)
    backend = DPSynthesizer(config=Config(proposals=160))
    solve(parse((ROOT / "examples/synthesis/dp_gp/knapsack.ae").read_text()), backend, budget=60)
    stage = backend.last_report["stages"][1]
    assert stage["epochs"] == 2
    assert stage["counterexamples"][0][0] == "update"


def test_emitted_algorithm_must_satisfy_the_original_result_refinement():
    source = (
        (ROOT / "examples/synthesis/dp_gp/knapsack.ae")
        .read_text()
        .replace("v <= 5}):Int := ?algorithm;", "v <= 5}):{r:Int | r < 0} := ?algorithm;")
    )
    with pytest.raises(SynthesisNotSuccessful, match="refinement validation"):
        solve(parse(source), DPSynthesizer(config=Config(proposals=160)), budget=60)


@pytest.mark.parametrize("change", ["effect", "domain", "shape", "witness", "empty", "floor"])
def test_unsupported_reference_contracts_fail_explicitly(change):
    source = (ROOT / "examples/synthesis/dp_gp/knapsack.ae").read_text()
    if change == "effect":
        source = source.replace(
            "def count(x:Int)(y:Int)(z:Int)(a:Int):Int := a;",
            'def count(x:Int)(y:Int)(z:Int)(a:Int):Int := native "a";',
        )
    elif change == "domain":
        source = source.replace("@dp_gp(reference, 4, 5)", "@dp_gp(reference, 3, 5)")
    elif change == "shape":
        source = source.replace("DP.reference n n capacity", "DP.reference (n + 1) n capacity")
    elif change == "witness":
        source = source.replace("v <= 5}):Int := ?algorithm;", "v <= 5}):Bool := ?algorithm;")
    elif change == "empty":
        source = source.replace("a = 0 || weight x <= y", "false")
    else:
        source = source.replace("objective 0 0 0 0;", "objective 0 0 0 1;")
    with pytest.raises(SynthesisNotSuccessful, match="[Uu]nsupported|requires|must|supports"):
        solve(parse(source), DPSynthesizer(), budget=10)
