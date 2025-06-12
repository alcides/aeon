from __future__ import annotations

import sys
import time
from typing import Any, Optional
from typing import Callable
from typing import TypeAlias

import multiprocess as mp
from loguru import logger

from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Term, Var
from aeon.core.types import Top
from aeon.core.types import top
from aeon.decorators import Metadata
from aeon.frontend.anf_converter import ensure_anf
from aeon.backend.evaluator import eval
from aeon.sugar.program import Definition
from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.identification import get_holes_info
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name

from aeon.synthesis.api import ErrorInSynthesis, Synthesizer, TimeoutInEvaluationException


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


def make_evaluators(ectx: EvaluationContext, fun_name: Name, metadata: Metadata) -> Evaluators:
    """Returns a list of functions that take the original program and return each fitness value"""

    fitness_decorators = ["minimize_int", "minimize_float", "multi_minimize_float"]
    used_decorators = [decorator for decorator in fitness_decorators if decorator in metadata.get(fun_name, [])]
    assert used_decorators, "No fitness decorators used in metadata for function."
    objectives_list: list[Definition] = [
        objective for decorator in used_decorators for objective in metadata.get(fun_name, [])[decorator]
    ]

    fitnesses: list[Callable[[Term], float]] = []
    for objective in objectives_list:

        def fitness(v: Term) -> float:
            program_for_fitness = substitution(v, Var(objective.name), Name("main", 0))
            try:
                result = eval(program_for_fitness, ectx)
            except Exception:
                result = sys.maxsize
            return result

        fitnesses.append(fitness)

    return fitnesses


def make_evaluator(
    ectx: EvaluationContext, replace: Callable[[Term], Term], evaluators: Evaluators, budget_eval: float = 1.0
) -> Callable[[Term], list[float]]:
    """Creates a function that takes candidate programs and return the fitness list."""

    def evaluate_individual(program: Any, result_queue: mp.Queue) -> Any:
        """Function to run in a separate process and places the result in a Queue."""
        start = time.time()
        try:
            results = [ev(program) for ev in evaluators]
            assert isinstance(results, list)
            assert results
            result_queue.put(results)
        except Exception as e:
            logger.log("SYNTHESIZER", f"Failed in the fitness function: {e}, {type(e)}")
            raise ErrorInSynthesis(e, msg=f"Failed in the fitness function: {e}, {type(e)}")
        finally:
            end = time.time()
            logger.info(f"Individual evaluation time: {end - start} ")

    def evaluate(candidate: Term, timeout: float = budget_eval) -> list[float]:
        prog = replace(candidate)
        result_queue = mp.Queue()
        eval_process = mp.Process(target=evaluate_individual, args=(prog, result_queue))
        eval_process.start()
        eval_process.join(timeout=timeout)

        if eval_process.is_alive():
            eval_process.terminate()
            eval_process.join()
            raise TimeoutInEvaluationException()
        else:
            fitness_values = result_queue.get()
            return fitness_values

    return evaluate


def synthesize(
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

    program_holes = get_holes_info(ctx, term, top, targets)

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

        t = synthesizer.synthesize(tyctx, ty, validator, evaluator, fun_name, metadata, budget, ui)
        mapping[hole_name] = t
    return mapping
