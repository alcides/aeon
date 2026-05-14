from __future__ import annotations

import math
import os
import queue as _queue
import sys
import time
import threading
from typing import Any, Optional
from typing import Callable
from typing import TypeAlias

import multiprocess as mp
from loguru import logger

from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Term, Var
from aeon.core.types import Top
from aeon.core.types import top, Type
from aeon.decorators import Metadata
from aeon.frontend.anf_converter import ensure_anf
from aeon.backend.evaluator import eval
from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.identification import get_holes_info
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name

from aeon.synthesis.api import ErrorInSynthesis, Synthesizer, TimeoutInEvaluationException
from aeon.synthesis.tactics.explicit_synth import ExplicitTacticSynthesizer

from aeon.synthesis.decorators import Goal
from aeon.synthesis.resource_meters import measure_cputime, measure_energy


def make_program(whole_program: Term, hole_name: Name) -> Callable[[Term], Term]:
    def replace(candidate: Term) -> Term:
        new_program = substitution(whole_program, candidate, hole_name)
        core_ast_anf = ensure_anf(new_program)
        return core_ast_anf

    return replace


def make_validator(ctx: TypingContext, replace: Callable[[Term], Term]) -> Callable[[Term], bool]:
    def validate(candidate: Term) -> bool:
        prog = replace(candidate)
        return check_type(ctx, prog, Top())

    return validate


Evaluators: TypeAlias = list[Callable[[Term], float]]


def _score_program(program: Any, evaluators: Evaluators, short_circuit: bool) -> list[float]:
    """Run the fitness evaluators against ``program``.

    Shared by both the legacy fork-per-call path and the persistent pool
    workers. With ``short_circuit`` the evaluators run in order and the
    loop stops at the first non-zero / non-finite score; the result is a
    single-element ``[n_goals - n_passed]`` list.
    """
    if short_circuit:
        n_goals = len(evaluators)
        passed = 0
        for ev in evaluators:
            try:
                score = float(ev(program))
            except Exception:
                break
            if not math.isfinite(score) or abs(score) >= 1e-9:
                break
            passed += 1
        return [float(n_goals - passed)]
    return [ev(program) for ev in evaluators]


def _pool_worker_loop(
    task_q: Any,
    result_q: Any,
    whole_program: Term,
    hole_name: Name,
    evaluators: Evaluators,
    short_circuit: bool,
) -> None:
    """Body of a persistent evaluation worker process.

    The worker receives ``whole_program`` / ``hole_name`` / ``evaluators``
    **once** at fork time. Each task is then just a small ``candidate``
    term: the worker substitutes it into the hole, ANF-converts, and
    scores. Sending only the candidate (not the whole substituted AST)
    keeps the per-call pickling cost tiny, and moves the
    ``substitution + ensure_anf`` work off the single main thread and
    into the (parallel) workers. A ``None`` task is the shutdown sentinel.
    """
    while True:
        candidate = task_q.get()
        if candidate is None:
            break
        try:
            program = ensure_anf(substitution(whole_program, candidate, hole_name))
            results = _score_program(program, evaluators, short_circuit)
            result_q.put(("ok", results))
        except Exception as e:  # pragma: no cover - defensive
            result_q.put(("err", f"{e}: {type(e)}"))


class PersistentEvalPool:
    """A pool of persistent worker processes for fitness evaluation.

    The naive design spawns a fresh ``mp.Process`` per candidate. On Linux
    that fork is actually cheap (copy-on-write), and crucially it passes
    the program AST to the child *for free* via shared memory — so the
    real per-candidate cost there is the fitness work itself.

    This pool keeps ``size`` workers alive and routes work to a free one
    via a thread-safe queue. To avoid re-pickling a large AST on every
    call, the workers are seeded with ``whole_program`` / ``hole_name``
    once at fork time; each task is just the small ``candidate`` term.
    The worker does the ``substitution + ensure_anf`` itself, which also
    parallelises that step across workers.

    Timeout safety is preserved: a worker that doesn't answer within the
    deadline is terminated and replaced, so a hung candidate can't poison
    the pool. ``evaluate`` is safe to call from multiple threads — each
    call exclusively holds one worker for its duration.

    Caveat: workers are reused, so a candidate that mutates process
    globals (e.g. via ``native_import``) leaks that state into later
    evaluations on the same worker. For the pure arithmetic / conditional
    candidates that synthesis explores this is a non-issue.
    """

    def __init__(
        self,
        whole_program: Term,
        hole_name: Name,
        evaluators: Evaluators,
        short_circuit: bool,
        size: int,
    ):
        assert size >= 1
        self._whole_program = whole_program
        self._hole_name = hole_name
        self._evaluators = evaluators
        self._short_circuit = short_circuit
        self._size = size
        self._free: _queue.Queue = _queue.Queue()
        self._all_lock = threading.Lock()
        self._all: list = []
        for _ in range(size):
            w = self._spawn()
            self._all.append(w)
            self._free.put(w)

    def _spawn(self) -> tuple:
        task_q: Any = mp.Queue()
        result_q: Any = mp.Queue()
        proc = mp.Process(
            target=_pool_worker_loop,
            args=(
                task_q,
                result_q,
                self._whole_program,
                self._hole_name,
                self._evaluators,
                self._short_circuit,
            ),
            daemon=True,
        )
        proc.start()
        return (proc, task_q, result_q)

    def evaluate(self, candidate: Term, timeout: float) -> list[float]:
        """Evaluate ``candidate`` on a free worker, blocking until one is
        available. Raises ``TimeoutInEvaluationException`` if the worker
        doesn't answer within ``timeout`` (and replaces that worker)."""
        worker = self._free.get()
        proc, task_q, result_q = worker
        replacement: Optional[tuple] = None
        try:
            task_q.put(candidate)
            try:
                status, payload = result_q.get(timeout=timeout)
            except _queue.Empty:
                # Hung (or just too-slow) candidate: kill + replace this worker.
                try:
                    proc.terminate()
                    proc.join()
                except Exception:
                    pass
                with self._all_lock:
                    if worker in self._all:
                        self._all.remove(worker)
                replacement = self._spawn()
                with self._all_lock:
                    self._all.append(replacement)
                raise TimeoutInEvaluationException()
            if status == "err":
                raise ErrorInSynthesis(payload, msg=f"Failed in the fitness function: {payload}")
            return payload
        finally:
            # Return the (possibly fresh) worker to the free pool.
            self._free.put(replacement if replacement is not None else worker)

    def shutdown(self) -> None:
        with self._all_lock:
            workers = list(self._all)
            self._all.clear()
        for proc, task_q, _result_q in workers:
            try:
                task_q.put(None)
            except Exception:
                pass
        for proc, _task_q, _result_q in workers:
            try:
                proc.join(timeout=1.0)
                if proc.is_alive():
                    proc.terminate()
            except Exception:
                pass


def eval_pool_size() -> int:
    """Worker count for the persistent eval pool, from ``AEON_TDSYN_PARALLEL``.

    Defaults to 1 — a single persistent worker, which still avoids the
    fork-per-candidate cost of the legacy path.
    """
    raw = os.environ.get("AEON_TDSYN_PARALLEL", "1")
    try:
        return max(1, int(raw))
    except ValueError:
        return 1



def _make_fitness(goal: Goal, ectx: EvaluationContext) -> Callable[[Term], float]:
    """Build a fitness function for a single goal, dispatching on ``goal.kind``."""

    def fitness(v: Term) -> float:
        program_for_fitness = substitution(v, Var(goal.function), Name("main", 0))
        try:
            if goal.kind == "cputime":
                return measure_cputime(lambda: eval(program_for_fitness, ectx))
            if goal.kind == "energy":
                return measure_energy(lambda: eval(program_for_fitness, ectx))
            return eval(program_for_fitness, ectx)
        except Exception:
            return sys.maxsize

    return fitness


def make_evaluators(ectx: EvaluationContext, fun_name: Name, metadata: Metadata) -> Evaluators:
    """Returns a list of functions that take the original program and return each fitness value"""

    goals: list[Goal] = metadata.get(fun_name, {}).get("goals", [])
    fitnesses: list[Callable[[Term], float]] = []
    for goal in goals:
        assert goal.length == 1, "Currently, we only support 1 fitness value per function"
        fitnesses.append(_make_fitness(goal, ectx))
    return fitnesses


def make_evaluator(
    ectx: EvaluationContext,
    replace: Callable[[Term], Term],
    evaluators: Evaluators,
    budget_eval: float = 1.0,
    short_circuit: bool = False,
    pool: Optional[PersistentEvalPool] = None,
) -> Callable[[Term], list[float]]:
    """Creates a function that takes candidate programs and returns the fitness list.

    When ``short_circuit`` is True, the evaluators are run in order and
    the loop stops at the first one that returns a non-zero (or
    non-finite) value. The wrapper then returns a *single*-element list
    ``[len(evaluators) - n_passed]``, to be minimised: 0 means every
    example passed, ``len(evaluators)`` means even the first example
    failed (or threw). This collapses an N-axis Pareto problem into a
    1-axis one, useful when exact correctness is required.

    If ``pool`` is given, candidates are dispatched to that persistent
    worker pool (no fork-per-call). Otherwise the legacy path spawns a
    fresh ``mp.Process`` per candidate.
    """

    def evaluate_individual(program: Any, result_queue: mp.Queue) -> Any:
        """Function to run in a separate process and places the result in a Queue."""
        start = time.time()
        try:
            results = _score_program(program, evaluators, short_circuit)
            assert isinstance(results, list)
            result_queue.put(results)
        except Exception as e:
            logger.log("SYNTHESIZER", f"Failed in the fitness function: {e}, {type(e)}")
            raise ErrorInSynthesis(e, msg=f"Failed in the fitness function: {e}, {type(e)}")
        finally:
            end = time.time()
            logger.info(f"Individual evaluation time: {end - start} ")

    def evaluate(candidate: Term, timeout: float = budget_eval) -> list[float]:
        if pool is not None:
            # Persistent pool: the worker does `replace` itself, so we only
            # pickle the small candidate term, not the whole substituted AST.
            return pool.evaluate(candidate, timeout)
        # Legacy path: fork a fresh process per candidate. `replace` runs
        # here in the parent; fork shares the result with the child for free.
        prog = replace(candidate)
        result_queue = mp.Queue()
        eval_process = mp.Process(target=evaluate_individual, args=(prog, result_queue))
        eval_process.start()
        eval_process.join(timeout=timeout)
        if eval_process.is_alive():
            eval_process.close()
            eval_process.terminate()
            eval_process.join()
            raise TimeoutInEvaluationException()
        else:
            fitness_values = result_queue.get()
            return fitness_values

    return evaluate


def synthesize_holes(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    targets: list[tuple[Name, list[Name]]],
    metadata: Metadata,
    synthesizer: Synthesizer,
    budget: float = 60.0,
    ui: SynthesisUI = SynthesisUI(),
    budget_eval: Optional[float] = None,
) -> dict[Name, Optional[Term]]:
    """Synthesizes code for multiple functions, each with multiple holes."""

    if budget_eval is None:
        budget_eval = max(budget / 1000, 1)

    program_holes = get_holes_info(ctx, term, top, targets, refined_types=True)

    mapping = {}

    for fun_name, holes_names in targets:
        assert len(holes_names) == 1, "Currently, we only support 1 hole per function"

        hole_name = holes_names[0]
        ty, tyctx = program_holes[hole_name]
        ui.start(tyctx, ectx, hole_name.name, ty, budget)

        replace = make_program(term, hole_name)
        if metadata.get(fun_name, {}).get("skip_typecheck", False):
            # @skip_typecheck — bypass the SMT typecheck per candidate.
            def validator(_term: Term) -> bool:
                return True
        else:
            validator = make_validator(ctx, replace)
        evaluators = make_evaluators(ectx, fun_name, metadata)
        short_circuit_flag = bool(metadata.get(fun_name, {}).get("short_circuit", False))
        # Persistent worker pool: workers are seeded with the whole program +
        # hole name once, so each candidate evaluation only ships the small
        # candidate term. Shut down in the finally below.
        pool = PersistentEvalPool(
            term, hole_name, evaluators, short_circuit_flag, eval_pool_size()
        )
        evaluator = make_evaluator(
            ectx, replace, evaluators, budget_eval, short_circuit=short_circuit_flag, pool=pool
        )
        assert isinstance(tyctx, TypingContext)
        assert isinstance(ty, Type)
        tac_map = metadata.get(fun_name, {}).get("tactic_scripts")
        steps = None
        if isinstance(tac_map, dict):
            raw = tac_map.get(hole_name)
            if raw is not None:
                steps = tuple(raw)
            elif len(tac_map) == 1:
                steps = tuple(next(iter(tac_map.values())))
        syn_impl: Synthesizer = ExplicitTacticSynthesizer(steps) if steps is not None else synthesizer
        try:
            t = syn_impl.synthesize(
                ctx=tyctx,
                type=ty,
                validate=validator,
                evaluate=evaluator,
                fun_name=fun_name,
                metadata=metadata,
                budget=budget,
                ui=ui,
            )
        except Exception as e:
            ui.end(None, None)
            raise e
        finally:
            pool.shutdown()

        ui.end(t, None)
        mapping[hole_name] = t
    return mapping
