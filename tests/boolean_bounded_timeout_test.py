"""Blocking compiler/solver calls must not escape the synthesis deadline."""

import os
import signal
from time import monotonic, sleep

import multiprocess as mp
import pytest
import z3

import aeon.synthesis.entrypoint as entrypoint
import aeon.synthesis.solver_problem as solver_problem
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.boolean_bounded import BooleanBoundedSynthesizer, BoundedBooleanFailure, _Template
from aeon.synthesis.uis.api import SilentSynthesisUI
from tests.boolean_bounded_test import direct, direct_problem
from tests.joint_hole_synthesis_test import parse, solve


class RecordingUI(SilentSynthesisUI):
    def __init__(self):
        self.solutions = []
        self.ends = []

    def register(self, solution, quality, elapsed_time, is_best):
        self.solutions.append(solution)

    def end(self, solution, quality):
        self.ends.append(solution)


@pytest.mark.parametrize(
    "phase",
    ["hole_types", "properties", "source", "obligations", "solver", "extraction", "validation", "final", "fitness"],
)
def test_entire_joint_run_is_contained(monkeypatch, phase):
    # Compile before injecting the block: the budget starts at synthesis entry.
    source = "@bounded_cnf(1) def f(x:Bool):{r:Bool | r = !x} := ?h;"
    if phase == "fitness":
        source += " @property(1) def law(x:Bool):Bool := f x = !x;"
    driver = parse(source)
    backend = BooleanBoundedSynthesizer()
    ui = RecordingUI()
    pid = mp.Value("i", 0)

    def block(*args, **kwargs):
        pid.value = os.getpid()
        # Exercise the shared worker's terminate -> kill escalation as well.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        sleep(30)

    patches = {
        "hole_types": (entrypoint, "get_holes_info"),
        "properties": (entrypoint, "property_corpora_for_targets"),
        "source": (BooleanBoundedSynthesizer, "check_source"),
        "obligations": (solver_problem, "build_solver_problem"),
        "solver": (z3.Solver, "check"),
        "extraction": (_Template, "extract"),
        "validation": (entrypoint, "check_type"),
    }
    if phase in patches:
        monkeypatch.setattr(*patches[phase], block)
    elif phase == "final":
        original = entrypoint.check_type
        calls = 0

        def final_check(*args, **kwargs):
            nonlocal calls
            calls += 1
            return block() if calls == 2 else original(*args, **kwargs)

        monkeypatch.setattr(entrypoint, "check_type", final_check)
    else:
        monkeypatch.setattr(entrypoint, "make_bundled_fitness_evaluator", lambda *args: block)

    started = monotonic()
    with pytest.raises(BoundedBooleanFailure) as exc:
        entrypoint.synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            incomplete_functions_and_holes(driver.typing_ctx, driver.core),
            driver.metadata,
            backend,
            budget=1,
            ui=ui,
        )
    elapsed = monotonic() - started
    assert exc.value.category == backend.report.status == "timeout"
    assert 0.9 <= elapsed < 3
    assert 0.9 <= backend.report.elapsed < 3
    assert pid.value > 0, f"did not reach injected {phase} block"
    assert not ui.solutions and ui.ends == [None]
    with pytest.raises(ProcessLookupError):
        os.kill(pid.value, 0)


def test_direct_validation_timeout_and_backend_reuse():
    holes, metadata, _ = direct_problem(1, [True] * 4)
    backend = BooleanBoundedSynthesizer()
    started = monotonic()
    with pytest.raises(BoundedBooleanFailure) as exc:
        direct(backend, holes, metadata, validate=lambda _: sleep(30), budget=0.2)
    assert exc.value.category == backend.report.status == "timeout"
    assert monotonic() - started < 2
    assert direct(backend, holes, metadata) is not None
    assert backend.report.status == "solved"


def test_final_rejection_does_not_publish_success(monkeypatch):
    driver = parse("@bounded_cnf(0) def f:Bool := ?h;")
    backend = BooleanBoundedSynthesizer()
    ui = RecordingUI()
    calls = 0

    def validate(*args):
        nonlocal calls
        calls += 1
        return calls == 1

    monkeypatch.setattr(entrypoint, "check_type", validate)
    with pytest.raises(BoundedBooleanFailure) as exc:
        entrypoint.synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            incomplete_functions_and_holes(driver.typing_ctx, driver.core),
            driver.metadata,
            backend,
            budget=2,
            ui=ui,
        )
    assert exc.value.category == backend.report.status == "validation_error"
    assert not ui.solutions and ui.ends == [None]


def test_worker_crash_is_not_timeout_or_unsat(monkeypatch):
    driver = parse("@bounded_cnf(0) def f:Bool := ?h;")
    backend = BooleanBoundedSynthesizer()
    monkeypatch.setattr(BooleanBoundedSynthesizer, "check_source", lambda *args: os._exit(1))
    with pytest.raises(BoundedBooleanFailure) as exc:
        solve(driver, backend, budget=2)
    assert exc.value.category == backend.report.status == "validation_error"
