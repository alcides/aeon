from __future__ import annotations

import time
from typing import Any, Optional
from typing import Callable
from typing import TypeAlias

import multiprocess as mp
from loguru import logger

import aeon.logger.logger  # noqa: F401  — registers custom levels (SYNTHESIZER etc.) at import.

from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
import dataclasses

from aeon.core.terms import Let, Rec, Term, Var
from aeon.core.types import Top
from aeon.core.types import top, Type
from aeon.decorators import Metadata
from aeon.backend.evaluator import eval
from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.identification import get_holes_info
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name

from aeon.synthesis.api import ErrorInSynthesis, InvalidIndividualException, Synthesizer, TimeoutInEvaluationException
from aeon.synthesis.tactics.explicit_synth import ExplicitTacticSynthesizer

from aeon.synthesis.decorators import Goal
from aeon.synthesis.resource_meters import measure_cputime, measure_energy


def make_program(whole_program: Term, hole_name: Name) -> Callable[[Term], Term]:
    def replace(candidate: Term) -> Term:
        return substitution(whole_program, candidate, hole_name)

    return replace


def make_validator(ctx: TypingContext, replace: Callable[[Term], Term]) -> Callable[[Term], bool]:
    def validate(candidate: Term) -> bool:
        prog = replace(candidate)
        return check_type(ctx, prog, Top())

    return validate


Evaluators: TypeAlias = list[Callable[[Term], float]]


def _set_program_tail(term: Term, new_tail: Term) -> Term:
    """Replace the innermost body of a chain of top-level ``let``/``rec``
    bindings with ``new_tail``, leaving the bindings (and hence everything in
    scope) intact."""
    if isinstance(term, Rec):
        return dataclasses.replace(term, body=_set_program_tail(term.body, new_tail))
    if isinstance(term, Let):
        return dataclasses.replace(term, body=_set_program_tail(term.body, new_tail))
    return new_tail


def _make_fitness(goal: Goal, ectx: EvaluationContext) -> Callable[[Term], float]:
    """Build a fitness function for a single goal, dispatching on ``goal.kind``."""

    def fitness(v: Term) -> float:
        # Evaluate the goal's objective function (a nullary top-level binding,
        # e.g. ``jaccard shape``) by making it the program's result. Replacing
        # the program tail works whether or not a ``main`` entry point is
        # present -- under ``--no-main`` there is none, and the previous
        # ``main``-substitution silently left the metric uncomputed (the program
        # evaluated to its placeholder tail instead of the objective).
        program_for_fitness = _set_program_tail(v, Var(goal.function))
        try:
            if goal.kind == "cputime":
                return measure_cputime(lambda: eval(program_for_fitness, ectx))
            if goal.kind == "energy":
                return measure_energy(lambda: eval(program_for_fitness, ectx))
            return eval(program_for_fitness, ectx)
        except Exception:
            # A candidate that crashes mid-evaluation has no well-defined
            # fitness. Returning ``sys.maxsize`` made it "infinitely good"
            # for ``@maximize_*`` and "infinitely bad" for ``@minimize_*``
            # at the same time — a hybrid the Pareto front cannot dominate,
            # so a single crash would lock in as "Best" forever (issue
            # #120). Raise the backend-neutral
            # ``InvalidIndividualException`` instead; synthesizer adapters
            # translate it into their search framework's notion of "drop
            # this candidate".
            raise InvalidIndividualException()

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
    ectx: EvaluationContext, replace: Callable[[Term], Term], evaluators: Evaluators, budget_eval: float = 1.0
) -> Callable[[Term], list[float]]:
    """Creates a function that takes candidate programs and return the fitness list."""

    def evaluate_individual(program: Any, result_queue: mp.Queue) -> Any:
        """Function to run in a separate process and places the result in a Queue."""
        start = time.time()
        try:
            try:
                results = [ev(program) for ev in evaluators]
                assert isinstance(results, list)
                result_queue.put(("ok", results))
            except InvalidIndividualException:
                result_queue.put(("invalid", None))
        except Exception as e:
            logger.log("SYNTHESIZER", f"Failed in the fitness function: {e}, {type(e)}")
            # Make sure the parent isn't left blocked on ``result_queue.get()``
            # if an unexpected exception escapes — propagate it as a typed
            # message so the parent re-raises ``ErrorInSynthesis``.
            result_queue.put(("error", f"{type(e).__name__}: {e}"))
            raise ErrorInSynthesis(e, msg=f"Failed in the fitness function: {e}, {type(e)}")
        finally:
            end = time.time()
            logger.info(f"Individual evaluation time: {end - start} ")

    def evaluate(candidate: Term, timeout: float = budget_eval) -> list[float]:
        # import faulthandler; faulthandler.enable()
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
        kind, payload = result_queue.get()
        if kind == "ok":
            return payload
        if kind == "invalid":
            raise InvalidIndividualException()
        raise ErrorInSynthesis(Exception(payload), msg=str(payload))

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
        validator = make_validator(ctx, replace)
        evaluators = make_evaluators(ectx, fun_name, metadata)
        evaluator = make_evaluator(ectx, replace, evaluators, budget_eval)
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

        ui.end(t, None)
        mapping[hole_name] = t
    return mapping
