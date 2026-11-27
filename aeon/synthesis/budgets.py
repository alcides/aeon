"""Deterministic CPython/SMT quotas for reproducible synthesis runs.

Count Aeon's Python opcodes, excluding UI and worker transport. Quotas are
version-specific: callers must pin CPython, Aeon and solver versions.
"""

from __future__ import annotations

from contextvars import ContextVar
from contextlib import contextmanager
from dataclasses import dataclass
from functools import wraps
from pathlib import Path
import platform
import sys
import math

from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.pareto import pick_pareto_member
from aeon.synthesis.uis.api import SynthesisUI


@dataclass(frozen=True)
class DeterministicBudget:
    opcodes: int
    evaluation_opcodes: int = 1_000_000
    smt_rlimit: int = 100_000
    cp_sat_work: float = 1.0

    def __post_init__(self):
        if platform.python_implementation() != "CPython":
            raise ValueError("Opcode budgets require CPython")
        if any(type(n) is not int or n <= 0 for n in (self.opcodes, self.evaluation_opcodes, self.smt_rlimit)):
            raise ValueError("Opcode and SMT resource budgets must be positive integers")
        if not math.isfinite(self.cp_sat_work) or self.cp_sat_work <= 0:
            raise ValueError("CP-SAT deterministic work must be positive and finite")


class OpcodeBudgetExceeded(BaseException):
    """Control flow that candidate-error handlers must not swallow."""


class EvaluationWatchdogExpired(SynthesisNotSuccessful):
    """A safety timeout is a failed run, never a candidate fitness result."""


_paused: ContextVar[bool] = ContextVar("opcode_budget_paused", default=False)
_policy: ContextVar[DeterministicBudget | None] = ContextVar("deterministic_synthesis_policy", default=None)
_fatal: ContextVar[list | None] = ContextVar("deterministic_synthesis_fatal", default=None)
_meter: ContextVar[object | None] = ContextVar("active_opcode_meter", default=None)


def consumed_opcodes():
    meter = _meter.get()
    return meter.used if isinstance(meter, OpcodeMeter) else 0


def raise_watchdog(message):
    error = EvaluationWatchdogExpired(message)
    failures = _fatal.get()
    if failures is not None:
        failures.append(error)
    raise error


def current_budget():
    return _policy.get()


@contextmanager
def budget_scope(policy):
    token = _policy.set(policy)
    failures = []
    fatal_token = _fatal.set(failures)
    try:
        yield
    finally:
        _policy.reset(token)
        _fatal.reset(fatal_token)
        if failures:
            raise failures[0]


def budget_context(function):
    @wraps(function)
    def wrapped(ctx, ectx, term, targets, metadata, synthesizer, *args, **kwargs):
        from dataclasses import replace
        from aeon.compilation.session import current_session
        from aeon.verification.state import VerificationState

        policy = getattr(synthesizer, "deterministic_budget", None)
        session = current_session()
        options = session.options
        previous_state = None
        override = policy is not None and options.smt_rlimit != policy.smt_rlimit
        if override:
            session.options = replace(options, smt_rlimit=policy.smt_rlimit)
            previous_state = session._states.pop(VerificationState, None)
        try:
            with budget_scope(policy):
                return function(ctx, ectx, term, targets, metadata, synthesizer, *args, **kwargs)
        finally:
            if override:
                session.options = options
                session._states.pop(VerificationState, None)
                if previous_state is not None:
                    session._states[VerificationState] = previous_state

    return wrapped


def prepare_deterministically(function):
    @wraps(function)
    def wrapped(*args, **kwargs):
        policy = current_budget()
        if policy is None:
            return function(*args, **kwargs)
        try:
            with OpcodeMeter(policy.opcodes).measure():
                return function(*args, **kwargs)
        except OpcodeBudgetExceeded:
            raise SynthesisNotSuccessful("Opcode budget exhausted while preparing synthesis examples")

    return wrapped


def evaluate_deterministically(function, *args):
    policy = current_budget()
    if policy is None:
        return function(*args)
    try:
        with OpcodeMeter(policy.evaluation_opcodes, include_foreign=True).measure():
            return function(*args)
    except OpcodeBudgetExceeded:
        from aeon.synthesis.api import TimeoutInEvaluationException

        raise TimeoutInEvaluationException("Candidate opcode budget exhausted")


_root = str(Path(__file__).resolve().parents[1]) + "/"
_excluded = (str(Path(__file__).resolve()), _root + "synthesis/uis/", _root + "logger/")


def unmetered(function):
    """Exclude scheduling, serialization and presentation from search work."""

    @wraps(function)
    def wrapped(*args, **kwargs):
        token = _paused.set(True)
        try:
            return function(*args, **kwargs)
        finally:
            _paused.reset(token)

    return wrapped


class OpcodeMeter:
    def __init__(self, limit: int, *, include_foreign: bool = False):
        self.limit = limit
        self.used = 0
        self.include_foreign = include_foreign

    def trace(self, frame, event, arg):
        if event == "call":
            filename = frame.f_code.co_filename
            if (
                (not self.include_foreign and not filename.startswith(_root))
                or filename.startswith(_excluded)
                or _paused.get()
            ):
                return None
            # Keep line events enabled: disabling them can suppress opcode
            # instrumentation on newly entered code in CPython 3.13.
            frame.f_trace_lines = True
            frame.f_trace_opcodes = True
            return self.trace
        if event == "line":
            # On a cold code object, CPython may not install opcode events
            # until the flag is set again at the first line event.
            frame.f_trace_opcodes = True
        if event == "opcode" and not _paused.get():
            if self.used >= self.limit:
                raise OpcodeBudgetExceeded()
            self.used += 1
        return self.trace

    def measure(self):
        return self

    def __enter__(self):
        self._previous_trace = sys.gettrace()
        self._pause_token = _paused.set(False)
        self._meter_token = _meter.set(self)
        # CPython 3.12 requires an opted-in frame before installing the trace.
        sys._getframe().f_trace_opcodes = True
        sys.settrace(self.trace)
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        # This module is unmetered, so quota exhaustion cannot interrupt its
        # own cleanup or the restoration of an existing debugger/coverage hook.
        sys.settrace(self._previous_trace)
        _meter.reset(self._meter_token)
        _paused.reset(self._pause_token)


class _BudgetUI(SynthesisUI):
    """Retain completed incumbents even if the opcode quota interrupts search."""

    def __init__(self, target, allow_unscored=True):
        self.target = target
        self.allow_unscored = allow_unscored
        self.front = []
        self.best = None

    @unmetered
    def start(self, typing_ctx, evaluation_ctx, target_name, target_type, budget):
        policy = current_budget()
        self.target.start(
            typing_ctx, evaluation_ctx, target_name, target_type, f"{policy.opcodes} opcodes" if policy else budget
        )

    @unmetered
    def end(self, solution, quality):
        if solution is not None and self.allow_unscored:
            self.best = solution
        self.target.end(solution, quality)

    @unmetered
    def register(self, solution, quality, elapsed_time, is_best):
        if is_best and solution is not None and quality != "Invalid" and (quality or self.allow_unscored):
            self.best = solution
        self.target.register(solution, quality, elapsed_time, is_best)

    @unmetered
    def register_front(self, front, elapsed_time):
        self.front = list(front)
        self.target.register_front(front, elapsed_time)

    @unmetered
    def progress(self, created, assessed, elapsed_time):
        self.target.progress(created, assessed, elapsed_time)

    @unmetered
    def report(self, report):
        self.target.report(report)


def run_budgeted_search(backend, operation, *, budget, ui, positional=(), mapping_names=None, **kwargs):
    def invoke(allowance, feedback):
        if positional:
            return operation(*positional, allowance, feedback, **kwargs)
        return operation(budget=allowance, ui=feedback, **kwargs)

    policy = getattr(backend, "deterministic_budget", None)
    if policy is None:
        return invoke(budget, ui)
    metadata = kwargs.get("metadata", positional[-1] if positional and isinstance(positional[-1], dict) else {})
    capture = _BudgetUI(ui, allow_unscored=not any(entry.get("goals") for entry in metadata.values()))
    meter = OpcodeMeter(policy.opcodes)
    exhausted = False
    try:
        with meter.measure():
            return invoke(float("inf"), capture)
    except OpcodeBudgetExceeded:
        exhausted = True
        if capture.front:
            backend.pareto_front = capture.front
            result = pick_pareto_member(capture.front, getattr(backend, "seed", 0))
        else:
            result = capture.best
        if result is not None:
            return dict(zip(mapping_names, result.terms)) if mapping_names is not None else result
        raise SynthesisNotSuccessful(f"Opcode budget exhausted ({policy.opcodes}) before finding a valid candidate")
    finally:
        ui.report({"backend": "opcode_budget", "opcodes": meter.used, "limit": policy.opcodes, "exhausted": exhausted})


def search_budget_label(backend, seconds):
    policy = getattr(backend, "deterministic_budget", None)
    return seconds if policy is None else f"{policy.opcodes} opcodes"


def pool_budget_options(backend):
    policy = getattr(backend, "deterministic_budget", None)
    return {} if policy is None else {"opcode_budget": policy.evaluation_opcodes, "strict_timeout": True}
