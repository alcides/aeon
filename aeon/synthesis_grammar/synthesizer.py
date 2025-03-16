from __future__ import annotations

import builtins
import configparser
import os
import sys
import time
from typing import Any, Tuple
from typing import Callable

import multiprocess as mp
from geneticengine.algorithms.gp.operators.combinators import ParallelStep, SequenceStep
from geneticengine.algorithms.gp.operators.crossover import GenericCrossoverStep
from geneticengine.algorithms.gp.operators.elitism import ElitismStep
from geneticengine.algorithms.gp.operators.initializers import StandardInitializer
from geneticengine.algorithms.gp.operators.mutation import GenericMutationStep
from geneticengine.algorithms.gp.operators.novelty import NoveltyStep
from geneticengine.algorithms.gp.operators.selection import LexicaseSelection
from geneticengine.algorithms.gp.operators.selection import TournamentSelection
from geneticengine.evaluation import SequentialEvaluator
from geneticengine.evaluation.budget import TimeBudget, TargetFitness, AnyOf, SearchBudget, TargetMultiFitness
from geneticengine.evaluation.recorder import SearchRecorder
from geneticengine.evaluation.tracker import (
    MultiObjectiveProgressTracker,
    ProgressTracker,
    SingleObjectiveProgressTracker,
)
from geneticengine.grammar import extract_grammar, Grammar
from geneticengine.prelude import GeneticProgramming, NativeRandomSource
from geneticengine.problems import MultiObjectiveProblem, Problem, SingleObjectiveProblem
from geneticengine.representations.tree.treebased import TreeBasedRepresentation
from geneticengine.solutions import Individual
from loguru import logger

from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Term, Literal, Var
from aeon.core.types import BaseType, Top, RefinedType
from aeon.core.types import Type
from aeon.core.types import top
from aeon.decorators import Metadata
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.program import Definition
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisUI
from aeon.synthesis_grammar.grammar import (
    gen_grammar_nodes,
    classType,
    find_class_by_name,
    process_type_name,
    build_control_flow_grammar_nodes,
)
from aeon.synthesis_grammar.identification import get_holes_info
from aeon.synthesis_grammar.recorder import LazyCSVRecorder, CSVRecorder
from aeon.synthesis_grammar.utils import representations, fitness_decorators, gengy_default_config
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


class SynthesisError(Exception):
    pass


MINIMIZE_OBJECTIVE = True
# TODO remove this if else statement if we invert the result of the maximize decorators
ERROR_NUMBER = (sys.maxsize - 1) if MINIMIZE_OBJECTIVE else -(sys.maxsize - 1)
ERROR_FITNESS = ERROR_NUMBER
TIMEOUT_DURATION: int = 60  # seconds


class TargetMultiSameFitness(SearchBudget):
    def __init__(self, target_fitness: float):
        self.target_fitness = target_fitness

    def is_done(self, tracker: ProgressTracker):
        assert isinstance(tracker, MultiObjectiveProgressTracker)
        comps = tracker.get_best_individuals()[0].get_fitness(tracker.get_problem()).fitness_components
        return all(abs(c - self.target_fitness) < 0.001 for c in comps)


def parse_config(config_file: str, section: str) -> dict[str, Any]:
    config = configparser.ConfigParser()
    try:
        config.read(config_file)
    except Exception as e:
        raise OSError(f"An error occurred while reading the file: {e}")

    assert section in config, f"Section '{section}' not found in the configuration file"
    gp_params = {k: builtins.eval(v) for k, v in config[section].items()}
    gp_params["config_name"] = section

    return gp_params


def is_valid_term_literal(term_literal: Term) -> bool:
    return (
        isinstance(term_literal, Literal)
        and term_literal.type == BaseType("Int")
        and isinstance(term_literal.value, int)
        and term_literal.value > 0
    )


def get_csv_file_path(file_path: str, representation: type, seed: int, hole_name: str, config_name: str) -> str | None:
    """Generate a CSV file path based on the provided file_path,
    representation, and seed.

    If file_path is empty, returns None.
    """
    if not file_path:
        return None

    file_name = os.path.basename(file_path)
    name_without_extension, _ = os.path.splitext(file_name)
    directory = os.path.join("csv", name_without_extension, representation.__class__.__name__)
    os.makedirs(directory, exist_ok=True)

    hole_suffix = f"_{hole_name}" if hole_name else ""
    csv_file_name = f"{name_without_extension}{hole_suffix}_{seed}_{config_name}.csv"

    return os.path.join(directory, csv_file_name)


def filter_nan_values(result):
    def isnan(obj):
        return obj != obj

    if isinstance(result, (float | int)):
        return ERROR_FITNESS if isnan(result) else result
    elif isinstance(result, list):
        return [ERROR_NUMBER if isnan(x) else x for x in result]
    else:
        return result


def individual_type_check(ctx, program, first_hole_name, individual_term):
    new_program = substitution(program, individual_term, first_hole_name)
    check_type_errors(ctx, new_program, Top())


def create_evaluator(
    ctx: TypingContext,
    ectx: EvaluationContext,
    program: Term,
    objectives_list: list[Definition],
    holes: list[str],
) -> Callable[[classType], Any]:
    """Creates the fitness function for a given synthesis context."""

    programs_to_evaluate: list[Term] = [
        substitution(program, Var(objective.name), "main") for objective in objectives_list
    ]

    def evaluate_individual(individual: classType, result_queue: mp.Queue) -> Any:
        """Function to run in a separate process and places the result in a Queue."""
        try:
            start = time.time()
            first_hole_name = holes[0]
            individual_term = individual.get_core()  # type: ignore
            individual_term = ensure_anf(individual_term, 10000000)
            individual_type_check(ctx, program, first_hole_name, individual_term)
            results = [eval(substitution(p, individual_term, first_hole_name), ectx) for p in programs_to_evaluate]
            result = results if len(results) > 1 else results[0]
            result = filter_nan_values(result)
            result_queue.put(result)
            end = time.time()
            logger.info(f"Individual evaluation time: {end - start} ")

        except Exception as e:
            logger.log("SYNTHESIZER", f"Failed in the fitness function: {e}, {type(e)}")
            result_queue.put(ERROR_FITNESS)

    def evaluator(individual: classType) -> Any:
        """Evaluates an individual with a timeout."""
        assert len(holes) == 1, "Only 1 hole per function is supported now"
        result_queue = mp.Queue()
        eval_process = mp.Process(target=evaluate_individual, args=(individual, result_queue))
        eval_process.start()
        eval_process.join(timeout=TIMEOUT_DURATION)

        if eval_process.is_alive():
            logger.log("SYNTHESIZER", "Timeout exceeded")
            eval_process.terminate()
            eval_process.join()
            return ERROR_FITNESS
        return result_queue.get()

    return evaluator


def is_multiobjective(used_decorators: list[str]) -> bool:
    return len(used_decorators) > 1 or used_decorators[0].startswith("multi")


def set_problem_type_and_error_fitness(metadata, used_fitness_decorators):
    global ERROR_FITNESS, ERROR_NUMBER
    fun_decorators = metadata.keys()

    ERROR_NUMBER = metadata["error_fitness"] if "error_fitness" in fun_decorators else ERROR_NUMBER

    if is_multiobjective(used_fitness_decorators):
        # TODO ver melhor
        ERROR_FITNESS = (
            [ERROR_NUMBER] * metadata["objective_number"] if "objective_number" in fun_decorators else [ERROR_NUMBER]
        )
        return MultiObjectiveProblem
    else:
        ERROR_FITNESS = ERROR_NUMBER
        return SingleObjectiveProblem


def get_target_fitness(metadata, problem_type):
    # FIXME: TargetMultiFitness is not supported yet! Only TargetMultiSameFitness is supported

    minimize = metadata.get("minimize", False) or metadata.get("multi_minimize", False)
    target_fitness = 0 if minimize else (sys.maxsize - 1)
    if isinstance(problem_type, MultiObjectiveProblem) and "objective_number" in metadata:
        target_fitness = [target_fitness] * metadata["objective_number"]
    return target_fitness, minimize


def get_function_objectives(used_fitness_decorators, fun_metadata) -> list[Definition]:
    return [objective for decorator in used_fitness_decorators for objective in fun_metadata[decorator]]


def problem_for_fitness_function(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    fun_name: str,
    metadata: Metadata,
    hole_names: list[str],
) -> Tuple[Problem, float | list[float]]:
    """Creates a problem for a particular function, based on the name and type
    of its fitness function."""

    fun_metadata = metadata.get(fun_name, {})
    if fun_metadata:
        used_fitness_decorators = [decorator for decorator in fitness_decorators if decorator in fun_metadata]
        assert used_fitness_decorators, f"No fitness decorators used for function {fun_name}."

        problem_type = set_problem_type_and_error_fitness(fun_metadata, used_fitness_decorators)

        objectives_list = get_function_objectives(used_fitness_decorators, fun_metadata)

        fitness_function = create_evaluator(ctx, ectx, term, objectives_list, hole_names)

        target_fitness, minimize = get_target_fitness(fun_metadata, problem_type)

        return problem_type(fitness_function=fitness_function, minimize=minimize), target_fitness
    else:
        return SingleObjectiveProblem(fitness_function=lambda x: 0, minimize=True), 0


def get_grammar_components(ctx: TypingContext, ty: Type, fun_name: str, metadata: Metadata):
    grammar_nodes = gen_grammar_nodes(ctx, fun_name, metadata, [])

    assert len(grammar_nodes) > 0
    assert isinstance(ty, (BaseType, RefinedType))  # TODO Synthesis: Support other types?
    hole_type_name = process_type_name(ty)
    grammar_nodes, starting_node = find_class_by_name("t_" + hole_type_name, grammar_nodes, ty)
    assert starting_node is not None, "Starting Node is None"
    grammar_nodes = (
        build_control_flow_grammar_nodes(grammar_nodes) if "allow_control_flow" in metadata[fun_name] else grammar_nodes
    )
    return grammar_nodes, starting_node


def create_grammar(holes: dict[str, tuple[Type, TypingContext]], fun_name: str, metadata: dict[str, Any]):
    assert len(holes) == 1, "More than one hole per function is not supported at the moment."
    hole_name = list(holes.keys())[0]
    ty, ctx = holes[hole_name]

    grammar_nodes, starting_node = get_grammar_components(ctx, ty, fun_name, metadata)
    return extract_grammar(grammar_nodes, starting_node)


def random_search_synthesis(grammar: Grammar, problem: Problem, budget: int = 1000) -> Term:
    """Performs a synthesis procedure with Random Search."""
    max_depth = 5
    rep = TreeBasedRepresentation(grammar, max_depth)
    r = NativeRandomSource(seed=42)

    population = [rep.create_genotype(r) for _ in range(budget)]
    population_with_score = [(problem.evaluate(phenotype), phenotype.get_core()) for phenotype in population]
    return min(population_with_score, key=lambda x: x[0])[1]


def create_gp_step(problem: Problem, gp_params: dict[str, Any]):
    """Creates the main GP step, using the provided parameters."""

    if isinstance(problem, MultiObjectiveProblem):
        selection = LexicaseSelection()
    else:
        selection = TournamentSelection(gp_params["tournament_size"])

    return ParallelStep(
        [
            ElitismStep(),
            NoveltyStep(),
            SequenceStep(
                selection,
                GenericCrossoverStep(gp_params["probability_crossover"]),
                GenericMutationStep(gp_params["probability_mutation"]),
            ),
        ],
        weights=[
            gp_params["n_elites"],
            gp_params["novelty"],
            gp_params["population_size"] - gp_params["n_elites"] - gp_params["novelty"],
        ],
    )


def set_budget(target_fitness, gp_params, tracker):
    budget = TimeBudget(time=gp_params["timer_limit"])

    if target_fitness is not None:
        if isinstance(tracker, SingleObjectiveProgressTracker):
            search_budget = TargetFitness(target_fitness)
        elif isinstance(tracker, MultiObjectiveProgressTracker) and isinstance(target_fitness, list):
            search_budget = TargetMultiFitness(target_fitness)
        elif isinstance(tracker, MultiObjectiveProgressTracker) and isinstance(target_fitness, (float, int)):
            search_budget = TargetMultiSameFitness(target_fitness)
        else:
            assert False

        budget = AnyOf(budget, search_budget)

    return budget


def set_tracker(problem, recorders):
    tracker = SingleObjectiveProgressTracker if isinstance(problem,
                                                           SingleObjectiveProblem) else MultiObjectiveProgressTracker

    return tracker(problem, evaluator=SequentialEvaluator(), recorders=recorders)


def geneticengine_synthesis(
    grammar: Grammar,
    problem: Problem,
    filename: str | None,
    hole_name: str,
    target_fitness: float | list[float],
    gp_params: dict[str, Any] | None = None,
    ui: SynthesisUI = SilentSynthesisUI(),
) -> Term:
    """Performs a synthesis procedure with GeneticEngine."""
    # gp_params = gp_params or parse_config("aeon/synthesis_grammar/gpconfig.gengy", "DEFAULT") # TODO
    gp_params = gp_params or gengy_default_config
    gp_params = dict(gp_params)
    representation_name = gp_params.pop("representation")
    config_name = gp_params.pop("config_name")
    seed = gp_params["seed"]
    assert isinstance(representation_name, str)
    assert isinstance(config_name, str)
    assert isinstance(seed, int)
    representation: type = representations[representation_name](grammar, max_depth=gp_params["max_depth"])

    tracker: ProgressTracker

    recorders = []
    if filename:
        csv_file_path = get_csv_file_path(filename, representation, seed, hole_name, config_name)
        csv_recorder = CSVRecorder if isinstance(target_fitness, list) else LazyCSVRecorder
        recorders.append(
            csv_recorder(csv_file_path, problem, only_record_best_individuals=gp_params["only_record_best_inds"])
        )

    tracker = set_tracker(problem, recorders)

    class UIBackendRecorder(SearchRecorder):
        def register(self, tracker: Any, individual: Individual, problem: Problem, is_best=False):
            ui.register(
                individual.get_phenotype().get_core(),
                individual.get_fitness(problem),
                tracker.get_elapsed_time(),
                is_best,
            )

    recorders.append(UIBackendRecorder())

    budget = set_budget(target_fitness, gp_params, tracker)

    alg = GeneticProgramming(
        problem=problem,
        budget=budget,
        representation=representation,  # type: ignore
        random=NativeRandomSource(seed),
        tracker=tracker,
        population_size=gp_params["population_size"],
        population_initializer=StandardInitializer(),
        step=create_gp_step(problem=problem, gp_params=gp_params),
    )

    ui.start(
        typing_ctx=None,  # type: ignore
        evaluation_ctx=None,  # type: ignore
        target_name=hole_name,
        target_type=None,  # type: ignore
        budget=gengy_default_config["timer_limit"],
    )
    best: Individual = alg.search()
    print(
        f"Fitness of {best.get_fitness(problem)} by genotype: {best.genotype} with phenotype: {best.get_phenotype()}",
    )
    ui.end(best.get_phenotype().get_core(), best.get_fitness(problem))
    return best.get_phenotype().get_core()


def synthesize_single_function(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    fun_name: str,
    holes: dict[str, tuple[Type, TypingContext]],
    metadata: Metadata,
    filename: str | None,
    synth_config: dict[str, Any] | None = None,
    ui: SynthesisUI = SynthesisUI(),
) -> Tuple[Term, Term]:
    # Step 1 Create a Single or Multi-Objective Problem instance.

    problem, target_fitness = problem_for_fitness_function(
        ctx,
        ectx,
        term,
        fun_name,
        metadata,
        list(holes.keys()),
    )

    # Step 2 Create grammar object.
    grammar = create_grammar(holes, fun_name, metadata)
    hole_name = list(holes.keys())[0]
    # TODO Synthesis: This function (and its parent) should be parameterized with the type of search procedure
    #  to use (e.g., Random Search, Genetic Programming, others...)

    # Step 3 Synthesize an element
    synthesized_element = geneticengine_synthesis(
        grammar, problem, filename, hole_name, target_fitness, synth_config, ui
    )
    # synthesized_element = random_search_synthesis(grammar, problem)

    # Step 4 Substitute the synthesized element in the original program and return it.
    return synthesized_element, substitution(term, synthesized_element, hole_name)


def synthesize(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    targets: list[tuple[str, list[str]]],
    metadata: Metadata,
    filename: str | None = None,
    synth_config: dict[str, Any] | None = None,
    refined_grammar: bool = False,
    ui: SynthesisUI = SynthesisUI(),
) -> Tuple[Term, dict[str, Term]]:
    """Synthesizes code for multiple functions, each with multiple holes."""

    program_holes = get_holes_info(ctx, term, top, targets, refined_grammar)
    assert len(program_holes) == len(targets), "No support for function with more than one hole"

    results = {}

    for name, holes_names in targets:
        hterm, term = synthesize_single_function(
            ctx,
            ectx,
            term,
            name,
            {h: v for h, v in program_holes.items() if h in holes_names},
            metadata,
            filename,
            synth_config,
            ui,
        )
        results[name] = hterm

    return term, results
