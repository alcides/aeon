"""ReGuS structure search, executable semantics, and backend-neutral goals."""

from dataclasses import replace
import math
from pathlib import Path

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp.server import SYNTHESIZERS
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import incomplete_functions_and_holes, iterate_top_level, term_has_holes
from aeon.synthesis.modules.genetic_programming import GeneticProgrammingSynthesizer
from aeon.synthesis.modules.regus import ReGuSSynthesizer
from aeon.synthesis.modules.regus.model import Episode, Event, Observation, Plan, decode, repairs
from aeon.synthesis.modules.regus.search import Config, Stats, code_successors, search, sketch_successors, utility
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


ROOT = Path(__file__).resolve().parents[1]

TOY = """
import ControlProgram; import ControlTask; import ControlRun;
import ControlReport; import ControlObservation; import Math;
def advance(choice:Int)(s:Int):Int := if choice = 0 then s + 1 else s - 1;
def cost(choice:Int)(s:Int):Float := if choice = DESIRED then 0.0 else 1.0;
def invalid(s:Int):Bool := false;
def sense(test:Int)(s:Int):Bool := if test = 0 then true else s < 2;
def abstract(s:Int):Int := 2 + (if s < 2 then 1 else 0);
def finish(remaining:Int)(status:Int)(s:Int):Float :=
    if status = 1 || status = 3 then 10000.0 else if status = 2 then 0.0 else 100.0 * Math.toFloat remaining;
def episode(p:ControlProgram):(ControlRun Int) :=
    ControlTask.run 2 2 4 advance cost invalid sense abstract 0 p;
def fitness(p:ControlProgram):Float := ControlTask.score finish (episode p);
def observe(p:ControlProgram):ControlObservation :=
    let r := ControlTask.record 2 2 4 advance cost invalid sense abstract 0 p in
    ControlObservation.snapshot 2 2 1 (ControlProgram.closed p)
        (ControlTask.report 4 (ControlTask.score finish r) r ControlReport.empty);
def feature(p:ControlProgram)(ignored:Int):ControlObservation := observe p;
@cluster(feature controller)
@minimize_float(fitness controller)
def controller:ControlProgram := let ControlProgram_gap := unit in ?controller;
def score(ignored:Int):Float := fitness controller;
def complete(ignored:Int):Bool := ControlProgram.closed controller;
"""


def parse(source):
    driver = AeonDriver(AeonConfig("regus", SilentSynthesisUI(), 1, no_main=True))
    errors = list(driver.parse(aeon_code=source))
    assert not errors, "\n".join(map(str, errors))
    return driver


def call(driver, name):
    names = {r.var_name.name: r.var_name for r in iterate_top_level(driver.core)}
    with driver.session.activate():
        return aeon_eval(
            set_program_tail(driver.core, Application(Var(names[name]), Literal(0, t_int))), driver.evaluation_ctx
        )


def solve(driver, backend, budget=1):
    with driver.session.activate():
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            incomplete_functions_and_holes(driver.typing_ctx, driver.core),
            driver.metadata,
            backend,
            budget,
            SilentSynthesisUI(),
        )
        for name, term in mapping.items():
            assert term is not None
            driver.core = substitution(driver.core, term, name)
    assert not term_has_holes(driver.core)
    return mapping


def test_factory_menu_and_seed(monkeypatch):
    monkeypatch.setenv("AEON_SEED", "19")
    backend = make_synthesizer("regus")
    assert isinstance(backend, ReGuSSynthesizer) and backend.seed == 19
    assert "regus" in SYNTHESIZERS


@pytest.mark.parametrize("desired", [0, 1])
def test_real_search_obeys_goals_defined_by_the_problem(desired):
    driver = parse(TOY.replace("DESIRED", str(desired)))
    backend = ReGuSSynthesizer(config=Config(max_loops=1, max_sketch_nodes=3, completion_batch=1))
    solve(driver, backend, budget=2)
    assert call(driver, "complete") is True
    assert call(driver, "score") == 0.0
    assert backend.stats.sketches >= 2 and backend.stats.complete > 0
    assert backend.stats.backpropagations > 0


def test_same_problem_runs_with_gp_without_translating_the_goal():
    driver = parse(TOY.replace("DESIRED", "0"))
    solve(driver, GeneticProgrammingSynthesizer(seed=0), budget=3)
    assert call(driver, "complete") is True
    assert math.isfinite(call(driver, "score"))


def test_execution_guided_search_learns_a_needed_conditional():
    source = (
        TOY.replace("DESIRED", "0")
        .replace("if choice = 0 then 0.0 else 1.0", "Math.toFloat ((s - 2) * (s - 2))")
        .replace("2 2 4", "2 2 8")
        .replace("ControlTask.report 4", "ControlTask.report 8")
    )
    # This plant needs feedback even on one start: a constant action overshoots
    # the target, whereas a branch can keep its state around the target.
    driver = parse(source)
    backend = ReGuSSynthesizer(config=Config(max_nodes=4, max_loops=1, max_sketch_nodes=2, completion_batch=1))
    mapping = solve(driver, backend, budget=8)
    assert call(driver, "score") <= 8.0
    assert backend.stats.branches > 0
    assert any("ControlProgram_branch" in str(term) for term in mapping.values())


@pytest.fixture(scope="module")
def semantics():
    return parse("""
    import ControlProgram; import ControlTask; import ControlRun;
    def advance(choice:Int)(s:Int):Int := if choice = 0 then s + 1 else s - 1;
    def cost(choice:Int)(s:Int):Float := 1.0;
    def invalid(s:Int):Bool := s < 0;
    def sense(test:Int)(s:Int):Bool := if test = 0 then true else if test = 1 then s < 2 else s > 0;
    def abstract(s:Int):Int := 4 + (if s < 2 then 2 else 0) + (if s > 0 then 1 else 0);
    def run(p:ControlProgram):(ControlRun Int) := ControlTask.run 2 3 8 advance cost invalid sense abstract 0 p;
    def two_phases:Int := ControlRun.state (run (ControlProgram.sequence
        (ControlProgram.loop 1 (ControlProgram.action 0)) (ControlProgram.loop 2 (ControlProgram.action 1))));
    def phase_steps(ignored:Int):Int := 8 - ControlRun.remaining (run (ControlProgram.sequence
        (ControlProgram.loop 1 (ControlProgram.action 0)) (ControlProgram.loop 2 (ControlProgram.action 1))));
    def phases(ignored:Int):Int := two_phases;
    def global_budget(ignored:Int):Int := ControlRun.remaining (run
        (ControlProgram.loop 0 (ControlProgram.sequence (ControlProgram.action 0) (ControlProgram.action 1))));
    def empty_loop(ignored:Int):Int := ControlRun.status (run (ControlProgram.loop 0 ControlProgram.halt));
    def breakpoint(ignored:Int):Int := ControlRun.blocked (run
        (ControlProgram.sequence (ControlProgram.action 0) ControlProgram.gap));
    def prefix_state(ignored:Int):Int := ControlRun.state (run
        (ControlProgram.sequence (ControlProgram.action 0) ControlProgram.gap));
    def last_failure(ignored:Int):Int := ControlRun.status
        (ControlTask.run 2 3 1 advance cost invalid sense abstract 0 (ControlProgram.action 1));
    def bad_action(ignored:Int):Int := ControlRun.status (run (ControlProgram.action 99));
    def bad_guard(ignored:Int):Int := ControlRun.status (run (ControlProgram.loop 99 ControlProgram.halt));
    """)


@pytest.mark.parametrize(
    "name,expected",
    [
        ("phases", 0),
        ("phase_steps", 4),
        ("global_budget", 0),
        ("empty_loop", 3),
        ("breakpoint", 3),
        ("prefix_state", 1),
        ("last_failure", 1),
        ("bad_action", 1),
        ("bad_guard", 1),
    ],
)
def test_controller_semantics_preserve_program_position_and_shared_fuel(semantics, name, expected):
    assert call(semantics, name) == expected


def test_nonfinite_cost_does_not_advance():
    driver = parse("""
    import ControlProgram; import ControlTask; import ControlRun;
    def advance(choice:Int)(s:Int):Int := s + 1;
    def cost(choice:Int)(s:Int):Float := native "float('nan')";
    def invalid(s:Int):Bool := false;
    def sense(test:Int)(s:Int):Bool := true;
    def abstract(s:Int):Int := 1;
    def state(ignored:Int):Int := ControlRun.state
        (ControlTask.run 1 1 1 advance cost invalid sense abstract 0 (ControlProgram.action 0));
    """)
    assert call(driver, "state") == 0


def test_lazy_branches_are_triggered_by_precondition_disagreement():
    plan = Plan("loop", 0, (Plan("action", 0),))
    first = Event(2, 0, 2, 3)
    changed = Event(2, 0, 3, 3)
    stable = Observation(2, 2, (Episode(0, 2, False, 1.0, (first, first)),))
    assert not repairs(plan, stable)
    proposed = repairs(plan, replace(stable, episodes=(Episode(0, 2, False, 1.0, (first, changed)),)))
    assert len(proposed) == 1
    branch = proposed[0].at(2)
    assert branch.kind == "branch" and branch.argument == 1
    assert branch.children == (Plan("gap"), Plan("action", 0))


def test_loop_sketches_are_separate_from_code_and_reached_gaps_expand_first():
    options = sketch_successors(Plan("sketch"), 2, Config())
    assert any(p.kind == "loop" for p in options)
    assert all(not p.contains("action") and not p.contains("branch") for p in options)
    plan = Plan("sequence", children=(Plan("gap"), Plan("gap")))
    observation = Observation(2, 1, (Episode(3, 0, False, 0.0, ()),))
    options = code_successors(plan, observation, ())
    assert options and all(p.at(2).kind == "gap" for p in options)
    assert all(not p.contains("branch") for p in options)


def test_existing_program_bindings_are_available_as_procedures():
    skill = Plan("skill", skill=Name("learned", 1))
    observation = Observation(1, 1, (Episode(1, 0, False, 0.0, ()),))
    assert skill in code_successors(Plan("gap"), observation, (skill,))


def test_open_program_hidden_in_a_procedure_is_never_returned():
    source = TOY.replace("DESIRED", "0").replace(
        "@cluster(feature controller)",
        "def unfinished:ControlProgram := ControlProgram.gap;\n@cluster(feature controller)",
    )
    driver = parse(source)
    solve(driver, ReGuSSynthesizer(config=Config(max_nodes=1, max_loops=0)), budget=0.5)
    assert call(driver, "complete") is True
    assert call(driver, "score") >= 300


def test_missing_observation_is_a_controlled_capability_error():
    source = TOY.replace("DESIRED", "0").replace("@cluster(feature controller)", "")
    with pytest.raises(UnsupportedSynthesisGoal, match="@cluster"):
        solve(parse(source), ReGuSSynthesizer())


@pytest.mark.parametrize(
    "kwargs",
    [
        {"max_nodes": 0},
        {"max_loops": -1},
        {"structure_cost": float("nan")},
        {"exploration": -1.0},
        {"evaluation_timeout": 0.0},
    ],
)
def test_invalid_configuration_is_rejected(kwargs):
    with pytest.raises(ValueError):
        Config(**kwargs)


def test_observation_worker_allowance_is_backend_local():
    backend = ReGuSSynthesizer(config=Config(evaluation_timeout=3.0))
    assert backend.evaluation_timeout(1.0) == 3.0
    assert backend.evaluation_timeout(10.0) == 10.0
    assert GeneticProgrammingSynthesizer().evaluation_timeout(1.0) == 1.0


@pytest.mark.parametrize(
    "task,module,program",
    [
        (
            "thermostat_structure",
            "ControlThermostat",
            """ControlProgram.loop 0
        (ControlProgram.branch 1 (ControlProgram.action 1)
            (ControlProgram.branch 2 (ControlProgram.action 0)
                (ControlProgram.branch 3 (ControlProgram.action 1) (ControlProgram.action 0))))""",
        ),
        (
            "pendulum_structure",
            "ControlPendulum",
            """ControlProgram.loop 0
        (ControlProgram.branch 1 (ControlProgram.action 3) (ControlProgram.action 0))""",
        ),
    ],
)
def test_problem_goals_preserve_the_reference_controller_loss(task, module, program):
    source = (ROOT / "examples/synthesis/control" / f"{task}.ae").read_text().replace("?controller", program)
    source += f"\ndef measured(ignored:Int):Float := training controller;\ndef expected(ignored:Int):Float := {module}.training {module}.reference;"
    driver = parse(source)
    assert call(driver, "measured") == pytest.approx(call(driver, "expected"))


@pytest.mark.parametrize("task,count", [("thermostat_structure", 4), ("pendulum_structure", 5)])
def test_problem_sensor_masks_agree_with_the_actual_predicates(task, count):
    source = (
        (ROOT / "examples/synthesis/control" / f"{task}.ae").read_text().replace("?controller", "ControlProgram.halt")
    )
    comparisons = [
        f"ControlTask.mask_from {count} sense ({start} {seed}) = abstract ({start} {seed})"
        for start in ("initial", "unseen")
        for seed in (0, 1)
    ]
    source += "\ndef consistent(ignored:Int):Bool := " + " && ".join(f"({c})" for c in comparisons) + ";"
    assert call(parse(source), "consistent") is True


def test_persistent_completer_queues_and_seeded_backpropagation():
    def run():
        stats = Stats()
        seen = []
        observation = Observation(1, 1, (Episode(0, 0, False, 0.0, ()),))

        def assess(plan):
            seen.append(plan)
            return (-float(plan.size), observation)

        search(
            assess,
            observation,
            seed=3,
            budget=0.05,
            config=Config(max_loops=1, max_sketch_nodes=2, max_nodes=5, completion_batch=1),
            stats=stats,
        )
        return stats, seen

    stats, seen = run()
    assert stats.sketches == 2 and stats.sketch_revisits > 0 and stats.backpropagations > 0
    assert len(seen) == len(set(seen))


def test_objective_orientation_and_bad_vectors():
    assert utility([1], [True]) > utility([2], [True])
    assert utility([2], [False]) > utility([1], [False])
    for score in ([float("nan")], [float("inf")], []):
        with pytest.raises(ValueError):
            utility(score, [True])


@pytest.mark.parametrize(
    "change",
    [
        lambda r: r[:1] + (0,) + r[2:],
        lambda r: r[:4] + ("yes",) + r[5:],
        lambda r: r[:5] + (("ControlReport_empty",),),
    ],
)
def test_malformed_protocol_is_rejected(change):
    raw = (
        "ControlObservation_snapshot",
        1,
        1,
        1,
        True,
        ("ControlReport_episode", 0, 0, False, 0.0, ("ControlTrace_empty",), ("ControlReport_empty",)),
    )
    assert decode(raw).closed
    with pytest.raises(ValueError):
        decode(change(raw))


def test_unsupported_target_has_a_controlled_error():
    driver = parse("@minimize_int(n) def n:Int := ?n;")
    with pytest.raises(UnsupportedSynthesisGoal, match="ControlProgram"):
        solve(driver, ReGuSSynthesizer())


@pytest.mark.parametrize("task", ["thermostat_structure", "pendulum_structure"])
def test_structure_problems_import_and_typecheck_outside_checkout(task, tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("AEONPATH", raising=False)
    driver = AeonDriver(AeonConfig("regus", SilentSynthesisUI(), 1, no_main=True))
    assert list(driver.parse(filename=str(ROOT / "examples/synthesis/control" / f"{task}.ae"))) == []
    assert driver.metadata and term_has_holes(driver.core)
