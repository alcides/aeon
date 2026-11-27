"""Mandatory synthesis examples bounded by opcodes and solver work, never seconds."""

import argparse
from pathlib import Path
import sys

import pytest
import z3

from aeon.__main__ import _parse_common_arguments, synthesis_requested
from aeon.compilation.session import CompilationOptions, CompilationSession
from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.budgets import (
    DeterministicBudget,
    EvaluationWatchdogExpired,
    OpcodeBudgetExceeded,
    OpcodeMeter,
)
from aeon.synthesis.evaluation_pool import EvaluationPool, OK, TIMEOUT
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.sugar.lifting import lift
from aeon.utils.pprint import pretty_print_sterm
from aeon.verification.limits import set_solver_limits


ROOT = Path(__file__).resolve().parent.parent
BACKENDS = ("enumerative", "random_search", "gp", "tdsyn_enumerative", "tdsyn_random", "smt")


class Reports(SilentSynthesisUI):
    def __init__(self):
        self.reports = []

    def report(self, report):
        self.reports.append(report)


def solve(backend, filename, *, seconds=60):
    ui = Reports()
    driver = AeonDriver(
        AeonConfig(
            backend,
            ui,
            seconds,
            no_main=True,
            deterministic_budget=DeterministicBudget(500_000),
        )
    )
    assert not list(driver.parse(filename=str(ROOT / filename)))
    assert driver.has_synth()
    driver.synth()
    return driver, ui


@pytest.mark.parametrize("backend", BACKENDS)
def test_refinement_example_is_solved_without_a_time_allowance(backend):
    # Zero seconds would prevent the old search from making progress.
    driver, ui = solve(backend, "examples/synthesis/int.ae", seconds=0)
    assert driver.core is not None
    assert ui.reports[-1]["opcodes"] <= 500_000


@pytest.mark.parametrize("backend", BACKENDS)
def test_optimizing_example_retains_incumbent_at_opcode_limit(backend):
    first, first_ui = solve(backend, "examples/synthesis/minimize_size.ae", seconds=0)
    second, second_ui = solve(backend, "examples/synthesis/minimize_size.ae", seconds=10_000)
    # Both final programs must typecheck and have exactly the same solution.
    assert pretty_print_sterm(lift(first.core)) == pretty_print_sterm(lift(second.core))
    assert first_ui.reports == second_ui.reports
    assert first_ui.reports[-1]["exhausted"]


def test_opcode_quota_escapes_candidate_exception_handlers_and_restores_trace():
    # This function is Aeon code, so the meter counts it (test code is excluded).
    from aeon.synthesis.fitness_eval import candidate_key

    previous = sys.gettrace()
    meter = OpcodeMeter(7)
    with pytest.raises(OpcodeBudgetExceeded):
        with meter.measure():
            try:
                while True:
                    candidate_key(Literal(1, t_int))
            except Exception:
                pytest.fail("candidate errors must not swallow opcode exhaustion")
    assert meter.used == 7
    assert sys.gettrace() is previous


def test_cold_and_warm_python_code_consume_the_same_opcodes():
    def computation():
        value = 0
        for number in range(10):
            value += number
        return value

    counts = []
    for _ in range(3):
        meter = OpcodeMeter(10_000, include_foreign=True)
        with meter.measure():
            assert computation() == 45
        counts.append(meter.used)
    assert counts[0] > 0
    assert len(set(counts)) == 1


def test_candidate_opcode_exhaustion_does_not_poison_worker():
    from aeon.backend.evaluator import eval as evaluate, EvaluationContext
    from aeon.core.terms import Application, Var
    from aeon.utils.name import Name

    name = Name("again", 0)
    ctx = EvaluationContext()
    divergent = Application(Var(name), Literal(0, t_int))
    ctx.variables[name] = lambda _x: evaluate(divergent, ctx)
    with_pool = EvaluationPool(
        lambda t: t,
        {"fitness": lambda t: evaluate(t, ctx)},
        budget_eval=5,
        opcode_budget=100,
        strict_timeout=True,
    )
    try:
        assert with_pool.run(divergent)["fitness"][0] == TIMEOUT
        assert with_pool.run(Literal(42, t_int))["fitness"] == (OK, 42)
    finally:
        with_pool.close()


def test_foreign_python_loop_uses_candidate_opcode_quota():
    def looping_python(_term):
        while True:
            pass

    pool = EvaluationPool(lambda t: t, {"fitness": looping_python}, opcode_budget=100, strict_timeout=True)
    try:
        assert pool.run(Literal(0, t_int))["fitness"] == (TIMEOUT, "opcode budget exhausted")
    finally:
        pool.close()


@pytest.mark.parametrize("backend", ("gp", "tdsyn_enumerative", "enumerative"))
def test_search_is_unchanged_when_reported_elapsed_time_jumps(backend, monkeypatch):
    from aeon.synthesis.modules import genetic_programming, native_search
    from aeon.synthesis.modules.tdsyn import synthesizer as tdsyn

    first, first_ui = solve(backend, "examples/synthesis/minimize_size.ae")
    monkeypatch.setattr(genetic_programming, "monotonic", lambda: 10**15)
    monkeypatch.setattr(native_search, "monotonic", lambda: 10**15)
    monkeypatch.setattr(tdsyn, "_get_elapsed_time", lambda _start: 10**15)

    def no_timing_probe(*args, **kwargs):
        pytest.fail("Deterministic GP must not size its population using timings")

    monkeypatch.setattr(genetic_programming, "choose_population_size", no_timing_probe)
    second, second_ui = solve(backend, "examples/synthesis/minimize_size.ae")
    assert pretty_print_sterm(lift(first.core)) == pretty_print_sterm(lift(second.core))
    assert first_ui.reports == second_ui.reports


def test_watchdog_is_not_swallowed_when_an_archive_already_has_an_incumbent():
    from types import SimpleNamespace
    from aeon.synthesis.candidate_archive import CandidateArchive
    from aeon.synthesis.decorators import Goal
    from aeon.utils.name import Name

    name = Name("f", 0)
    metadata = {name: {"goals": [Goal(minimize=True, length=1, function=name)]}}

    def scores(candidate):
        if candidate.value == 1:
            raise EvaluationWatchdogExpired("watchdog")
        return [0.0]

    archive = CandidateArchive(SimpleNamespace(seed=0), name, metadata, scores, 60, SilentSynthesisUI())
    with pytest.raises(EvaluationWatchdogExpired):
        archive.search(iter([Literal(0, t_int), Literal(1, t_int)]), lambda _candidate: True)


def test_worker_watchdog_aborts_instead_of_rejecting_a_candidate(monkeypatch):
    from aeon.synthesis.evaluation_pool import _ResultReader

    pool = EvaluationPool(lambda t: t, {"fitness": lambda t: []}, strict_timeout=True)
    try:

        def failed_reply(*args, **kwargs):
            raise EOFError("failed worker reply")

        monkeypatch.setattr(_ResultReader, "read", failed_reply)
        with pytest.raises(EvaluationWatchdogExpired, match="deterministic synthesis aborted"):
            pool.run(Literal(0, t_int))
    finally:
        pool.close()


def test_smt_quota_is_used_instead_of_timeout():
    options = CompilationOptions(smt_timeout_ms=1, smt_rlimit=1)
    with CompilationSession(options).activate():
        solver = z3.Solver()
        set_solver_limits(solver, 1)
        x = z3.Int("x")
        solver.add(x * x == 2)
        assert solver.check() == z3.unknown
        assert "resource" in solver.reason_unknown() or "max. resource" in solver.reason_unknown()


def test_lazy_solver_retains_its_owners_resource_quota():
    from aeon.verification.state import VerificationState

    session = CompilationSession(CompilationOptions(smt_rlimit=1))
    state = session.state(VerificationState)
    solver = state.get_solver()
    x = z3.Int("outside_session")
    solver.add(x * x == 2)
    assert solver.check() == z3.unknown


def test_unsupported_backend_fails_explicitly():
    driver = AeonDriver(
        AeonConfig(
            "llm_type_constrained",
            SilentSynthesisUI(),
            0,
            no_main=True,
            deterministic_budget=DeterministicBudget(1000),
        )
    )
    assert not list(driver.parse(aeon_code="def n : Int := ?hole;"))
    assert driver.has_synth()
    with pytest.raises(SynthesisNotSuccessful, match="does not support deterministic"):
        driver.synth()


def test_cli_recognizes_opcode_budget_and_disallows_competing_deadlines():
    parser = argparse.ArgumentParser()
    _parse_common_arguments(parser)
    assert parser.parse_args(["--opcode-budget", "1000"]).opcode_budget == 1000
    assert synthesis_requested(["--opcode-budget=1000"])
    with pytest.raises(SystemExit):
        parser.parse_args(["--opcode-budget", "0"])
    with pytest.raises(SystemExit):
        parser.parse_args(["--opcode-budget", "1000", "--budget", "1"])
