"""Pure Aeon control models: physics, bounded rollouts, and synthesis wiring."""

import math
from pathlib import Path

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import t_int, t_unit, top
from aeon.core.substitutions import substitution
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import (
    get_holes_info,
    incomplete_functions_and_holes,
    iterate_top_level,
    term_has_holes,
)
from aeon.synthesis.joint import JointCandidate, JointSynthesizer
from aeon.synthesis.modules.genetic_programming import GeneticProgrammingSynthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI


ROOT = Path(__file__).resolve().parents[1]


def parse(source):
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 1, no_main=True))
    errors = list(driver.parse(aeon_code=source))
    assert not errors, "\n".join(map(str, errors))
    return driver


def call(driver, name):
    names = {r.var_name.name: r.var_name for r in iterate_top_level(driver.core)}
    expression = Application(Var(names[name]), Literal(0, t_int))
    with driver.session.activate():
        return aeon_eval(set_program_tail(driver.core, expression), driver.evaluation_ctx)


@pytest.fixture(scope="module")
def models():
    probes = {
        "cart_x": (
            "Float",
            "ControlCartPole.position (ControlCartPole.step (ControlCartPole.mk 0.0 0.0 0.0 0.0) true)",
        ),
        "cart_v": (
            "Float",
            "ControlCartPole.velocity (ControlCartPole.step (ControlCartPole.mk 0.0 0.0 0.0 0.0) true)",
        ),
        "cart_rate": (
            "Float",
            "ControlCartPole.angular_velocity (ControlCartPole.step (ControlCartPole.mk 0.0 0.0 0.0 0.0) true)",
        ),
        "pend_angle": ("Float", "ControlPendulum.angle (ControlPendulum.step (ControlPendulum.mk 0.0 0.0) 100.0)"),
        "pend_rate": ("Float", "ControlPendulum.velocity (ControlPendulum.step (ControlPendulum.mk 0.0 0.0) 100.0)"),
        "pend_limit": ("Float", "ControlPendulum.velocity (ControlPendulum.step (ControlPendulum.mk 1.0 8.0) 2.0)"),
        "cruise_speed": (
            "Float",
            "ControlCruise.speed (ControlCruise.step (ControlCruise.mk 20.0 0.0 22.0 0.0) 100.0)",
        ),
        "cruise_integral": (
            "Float",
            "ControlCruise.integral (ControlCruise.step (ControlCruise.mk 0.0 19.9 22.0 0.0) 0.0)",
        ),
        "cruise_stop": (
            "Float",
            "ControlCruise.speed (ControlCruise.step (ControlCruise.mk 0.0 0.0 22.0 0.0) (0.0 - 100.0))",
        ),
        "heat": (
            "Float",
            "ControlThermostat.temperature (ControlThermostat.step (ControlThermostat.mk 20.0 false 10.0) true)",
        ),
        "cool": (
            "Float",
            "ControlThermostat.temperature (ControlThermostat.step (ControlThermostat.mk 20.0 true 10.0) false)",
        ),
        "stay_on": ("Bool", "ControlThermostat.reference 22.0 true"),
        "stay_off": ("Bool", "ControlThermostat.reference 22.0 false"),
        "wrap_positive": ("Float", "Control.angle 15.707963267948966"),
        "wrap_negative": ("Float", "Control.angle (0.0 - 15.707963267948966)"),
    }
    source = "import Control; import ControlCartPole; import ControlPendulum; import ControlCruise; import ControlThermostat;\n"
    for name, (ty, expression) in probes.items():
        source += f"def {name}(ignored:Int):{ty} := {expression};\n"
    for module, baseline in [
        ("ControlCartPole", "left"),
        ("ControlPendulum", "idle"),
        ("ControlCruise", "coast"),
        ("ControlThermostat", "off"),
    ]:
        for split in ("training", "held_out"):
            for policy in ("reference", baseline):
                source += f"def {module}_{split}_{policy}(ignored:Int):Float := {module}.{split} {module}.{policy};\n"
    return parse(source)


@pytest.mark.parametrize(
    "name,expected",
    [
        ("cart_x", 0.0),
        ("cart_v", 0.1951219512195122),
        ("cart_rate", -0.2926829268292683),
        ("pend_angle", 0.015),
        ("pend_rate", 0.3),
        ("pend_limit", 8.0),
        ("cruise_speed", 20.2),
        ("cruise_integral", 20.0),
        ("cruise_stop", 0.0),
        ("heat", 20.7),
        ("cool", 19.5),
        ("wrap_positive", -math.pi),
        ("wrap_negative", -math.pi),
    ],
)
def test_known_transitions_and_action_limits(models, name, expected):
    assert call(models, name) == pytest.approx(expected)


def test_thermostat_retains_memory_between_thresholds(models):
    assert call(models, "stay_on") is True
    assert call(models, "stay_off") is False


@pytest.mark.parametrize(
    "module,baseline",
    [
        ("ControlCartPole", "left"),
        ("ControlPendulum", "idle"),
        ("ControlCruise", "coast"),
        ("ControlThermostat", "off"),
    ],
)
def test_reference_improves_training_and_unseen_longer_episodes(models, module, baseline):
    for split in ("training", "held_out"):
        reference = call(models, f"{module}_{split}_reference")
        idle = call(models, f"{module}_{split}_{baseline}")
        assert math.isfinite(reference) and 0 <= reference < idle


def test_rollout_checks_last_transition_and_stops_on_failure():
    driver = parse("""
    import Control;
    def advance(s:Int):Int := s + 1;
    def cost(s:Int):Float := 1.0;
    def invalid(s:Int):Bool := s >= 2;
    def short(ignored:Int):Float := Control.loss (Control.rollout 1 advance cost invalid 0);
    def final_failure(ignored:Int):Bool := Control.failed (Control.rollout 2 advance cost invalid 0);
    def early_steps(ignored:Int):Int := Control.steps (Control.rollout 10 advance cost invalid 0);
    def failure_loss(ignored:Int):Float := Control.loss (Control.rollout 10 advance cost invalid 0);
    def empty(ignored:Int):Int := Control.steps (Control.rollout 0 advance cost invalid 0);
    def initially_invalid(ignored:Int):Bool := Control.failed (Control.rollout 0 advance cost invalid 2);
    """)
    assert call(driver, "short") == 1.0
    assert call(driver, "final_failure") is True
    assert call(driver, "early_steps") == 2
    assert call(driver, "failure_loss") >= 1_000_000
    assert call(driver, "empty") == 0
    assert call(driver, "initially_invalid") is True


def test_nonfinite_cost_is_penalized():
    driver = parse("""
    import Control;
    def advance(s:Int):Int := s + 1;
    def cost(s:Int):Float := native "float('nan')";
    def invalid(s:Int):Bool := false;
    def failed(ignored:Int):Bool := Control.failed (Control.rollout 5 advance cost invalid 0);
    def loss(ignored:Int):Float := Control.loss (Control.rollout 5 advance cost invalid 0);
    """)
    assert call(driver, "failed") is True
    assert call(driver, "loss") == 1_000_000


@pytest.mark.parametrize("task", ["cartpole", "pendulum", "cruise_control", "thermostat", "thermostat_free"])
def test_synthesis_tasks_compile_from_outside_checkout(task, tmp_path, monkeypatch):
    source = ROOT / "examples/synthesis/control" / f"{task}.ae"
    monkeypatch.delenv("AEONPATH", raising=False)
    monkeypatch.chdir(tmp_path)
    driver = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 1, no_main=True))
    assert list(driver.parse(filename=str(source))) == []
    assert term_has_holes(driver.core)
    assert driver.metadata


def test_new_control_runtime_is_aeon_only():
    for source in (ROOT / "aeon/libraries").glob("Control*.ae"):
        assert "native" not in source.read_text()


def solve(driver, backend, budget):
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


@pytest.mark.parametrize(
    "task,values",
    [
        ("cartpole", [10, 2]),
        ("pendulum", [8, 2, 1]),
        ("cruise_control", [4, 2]),
        ("thermostat", [21, 22]),
    ],
)
def test_joint_parameters_are_validated_and_scored_on_real_rollouts(task, values):
    driver = parse((ROOT / "examples/synthesis/control" / f"{task}.ae").read_text())

    class Inspect(JointSynthesizer):
        def synthesize_joint(self, holes, validate, evaluate, fun_name, metadata, budget, ui):
            candidate = JointCandidate(tuple(Literal(n, t_int) for n in values))
            outside_domain = JointCandidate((Literal(-100, t_int), *candidate.terms[1:]))
            assert not validate(outside_domain)
            assert validate(candidate)
            fitness = evaluate(candidate)
            assert len(fitness) == 1 and math.isfinite(fitness[0]) and fitness[0] >= 0
            return candidate

    solve(driver, Inspect(), 1)
    assert math.isfinite(call(driver, "held_out_loss"))


def test_actual_gp_completes_thermostat_parameters():
    driver = parse((ROOT / "examples/synthesis/control/thermostat.ae").read_text())
    solve(driver, GeneticProgrammingSynthesizer(seed=0), 2)
    assert math.isfinite(call(driver, "held_out_loss"))


def test_free_policy_cannot_call_reference_solution_or_rollouts():
    driver = parse((ROOT / "examples/synthesis/control/thermostat_free.ae").read_text())
    with driver.session.activate():
        holes = get_holes_info(
            driver.typing_ctx,
            driver.core,
            top,
            incomplete_functions_and_holes(driver.typing_ctx, driver.core),
        )
    assert len(holes) == 1
    _, context = next(iter(holes.values()))
    available = {name.name: ty for name, ty in context.concrete_vars()}
    for name in ("ControlThermostat_reference", "ControlThermostat_hysteresis", "Control_rollout", "Control_simulate"):
        assert available[name] == t_unit
    assert "cold" in available and "hot" in available
