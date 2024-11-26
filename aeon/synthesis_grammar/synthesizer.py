from __future__ import annotations

import builtins
import csv
import os
import sys
import time
from io import TextIOWrapper
from typing import Any, Tuple, Optional
from typing import Callable

import configparser
import multiprocess as mp
from geneticengine.algorithms.gp.operators.combinators import ParallelStep, SequenceStep
from geneticengine.algorithms.gp.operators.crossover import GenericCrossoverStep
from geneticengine.algorithms.gp.operators.elitism import ElitismStep
from geneticengine.algorithms.gp.operators.initializers import (
    StandardInitializer, )
from geneticengine.algorithms.gp.operators.mutation import GenericMutationStep
from geneticengine.algorithms.gp.operators.novelty import NoveltyStep
from geneticengine.algorithms.gp.operators.selection import LexicaseSelection
from geneticengine.algorithms.gp.operators.selection import TournamentSelection
from geneticengine.evaluation import SequentialEvaluator
from geneticengine.evaluation.budget import TimeBudget, TargetFitness, AnyOf, SearchBudget, TargetMultiFitness
from geneticengine.evaluation.recorder import SearchRecorder, FieldMapper
from geneticengine.evaluation.tracker import (
    MultiObjectiveProgressTracker,
    ProgressTracker,
    SingleObjectiveProgressTracker,
)
from geneticengine.grammar import extract_grammar, Grammar
from geneticengine.prelude import GeneticProgramming, NativeRandomSource
from geneticengine.problems import MultiObjectiveProblem, Problem, SingleObjectiveProblem
from geneticengine.random.sources import RandomSource
from geneticengine.representations.grammatical_evolution.dynamic_structured_ge import (
    DynamicStructuredGrammaticalEvolutionRepresentation, )
from geneticengine.representations.grammatical_evolution.ge import GrammaticalEvolutionRepresentation
from geneticengine.representations.grammatical_evolution.structured_ge import (
    StructuredGrammaticalEvolutionRepresentation, )
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
from aeon.typechecking import elaborate_and_check_type_errors
from aeon.typechecking.context import TypingContext


# TODO add timer to synthesis
class SynthesisError(Exception):
    pass


MINIMIZE_OBJECTIVE = True
# TODO remove this if else statement if we invert the result of the maximize decorators
ERROR_NUMBER = (sys.maxsize - 1) if MINIMIZE_OBJECTIVE else -(sys.maxsize - 1)
ERROR_FITNESS = ERROR_NUMBER
TIMEOUT_DURATION: int = 60  # seconds

representations = {
    "tree": TreeBasedRepresentation,
    "ge": GrammaticalEvolutionRepresentation,
    "sge": StructuredGrammaticalEvolutionRepresentation,
    "dsge": DynamicStructuredGrammaticalEvolutionRepresentation,
}

gengy_default_config = {
    "seed": 123,
    "verbose": 2,
    "config_name": "DEFAULT",
    # Stopping criteria
    "timer_stop_criteria": True,
    "timer_limit": 60,
    # Recording
    "only_record_best_inds": False,
    # Representation
    "representation": "tree",
    "max_depth": 8,
    # Population and Steps
    "population_size": 20,
    "n_elites": 1,
    "novelty": 1,
    "probability_mutation": 0.01,
    "probability_crossover": 0.9,
    "tournament_size": 5,
}


class TargetMultiSameFitness(SearchBudget):

    def __init__(self, target_fitness: float):
        self.target_fitness = target_fitness

    def is_done(self, tracker: ProgressTracker):
        assert isinstance(tracker, MultiObjectiveProgressTracker)
        comps = (tracker.get_best_individuals()[0].get_fitness(
            tracker.get_problem(), ).fitness_components)
        return all(abs(c - self.target_fitness) < 0.001 for c in comps)


class LazyCSVRecorder(SearchRecorder):

    def __init__(
        self,
        csv_path: str,
        problem: Problem,
        fields: dict[str, FieldMapper] = None,
        extra_fields: dict[str, FieldMapper] = None,
        only_record_best_individuals: bool = True,
    ):
        assert csv_path is not None
        self.csv_writer: Optional[Any] = None
        self.csv_file: Optional[TextIOWrapper] = None
        self.csv_file_path = csv_path
        self.fields = fields
        self.extra_fields = extra_fields
        self.only_record_best_individuals = only_record_best_individuals
        self.problem = problem
        self.header_printed = False
        if fields is not None:
            self.fields = fields

    def register(
        self,
        tracker: Any,
        individual: Individual,
        problem: Problem,
        is_best=True,
    ):
        if self.csv_file is None:
            self.csv_file = open(self.csv_file_path, "w", newline="")
            self.csv_writer = csv.writer(self.csv_file)
            if self.fields is None:
                self.fields = {
                    "Execution Time":
                    lambda t, i, _:
                    (time.monotonic_ns() - t.start_time) * 0.000000001,
                    "Fitness Aggregated":
                    lambda t, i, p: i.get_fitness(p).maximizing_aggregate,
                    "Phenotype":
                    lambda t, i, _: i.get_phenotype(),
                }
                for comp in range(problem.number_of_objectives()):
                    self.fields[
                        f"Fitness{comp}"] = lambda t, i, p: i.get_fitness(
                            p, ).fitness_components[comp]
            if self.extra_fields is not None:
                for name in self.extra_fields:
                    self.fields[name] = self.extra_fields[name]
            self.csv_writer.writerow([name for name in self.fields])
            self.csv_file.flush()
        if not self.only_record_best_individuals or is_best:
            self.csv_writer.writerow([
                self.fields[name](tracker, individual, problem)
                for name in self.fields
            ], )
            self.csv_file.flush()


def parse_config(config_file: str, section: str) -> dict[str, Any]:
    config = configparser.ConfigParser()
    try:
        config.read(config_file)
    except Exception as e:
        raise OSError(f"An error occurred while reading the file: {e}")

    assert section in config, f"Section '{section}' not found in the configuration file"
    gp_params = {}
    gp_params = {k: builtins.eval(v) for k, v in config[section].items()}
    gp_params["config_name"] = section

    return gp_params


def is_valid_term_literal(term_literal: Term) -> bool:
    return (isinstance(term_literal, Literal)
            and term_literal.type == BaseType("Int")
            and isinstance(term_literal.value, int) and term_literal.value > 0)


def get_csv_file_path(
    file_path: str,
    representation: type,
    seed: int,
    hole_name: str,
    config_name: str,
) -> str | None:
    """Generate a CSV file path based on the provided file_path,
    representation, and seed.

    If file_path is empty, returns None.
    """
    if not file_path:
        return None

    file_name = os.path.basename(file_path)
    name_without_extension, _ = os.path.splitext(file_name)
    directory = os.path.join(
        "csv",
        name_without_extension,
        representation.__class__.__name__,
    )
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
    elaborate_and_check_type_errors(ctx, new_program, Top())


def create_evaluator(
    ctx: TypingContext,
    ectx: EvaluationContext,
    program: Term,
    fun_name: str,
    metadata: Metadata,
    holes: list[str],
) -> Callable[[classType], Any]:
    """Creates the fitness function for a given synthesis context."""
    fitness_decorators = [
        "minimize_int",
        "minimize_float",
        "multi_minimize_float",
    ]
    used_decorators = [
        decorator for decorator in fitness_decorators
        if decorator in metadata[fun_name]
    ]
    assert used_decorators, "No fitness decorators used in metadata for function."

    objectives_list: list[Definition] = [
        objective for decorator in used_decorators
        for objective in metadata[fun_name][decorator]
    ]
    programs_to_evaluate: list[Term] = [
        substitution(program, Var(objective.name), "main")
        for objective in objectives_list
    ]

    def evaluate_individual(
        individual: classType,
        result_queue: mp.Queue,
    ) -> Any:
        """Function to run in a separate process and places the result in a Queue."""
        try:
            start = time.time()
            first_hole_name = holes[0]
            individual_term = individual.get_core()  # type: ignore
            individual_term = ensure_anf(individual_term, 10000000)
            individual_type_check(
                ctx,
                program,
                first_hole_name,
                individual_term,
            )
            results = [
                eval(substitution(p, individual_term, first_hole_name), ectx)
                for p in programs_to_evaluate
            ]
            result = results if len(results) > 1 else results[0]
            result = filter_nan_values(result)
            result_queue.put(result)
            end = time.time()
            logger.info(f"Individual evaluation time: {end-start} ")

        except Exception as e:
            # import traceback
            # traceback.print_exc()
            logger.log(
                "SYNTHESIZER",
                f"Failed in the fitness function: {e}, {type(e)}",
            )
            result_queue.put(ERROR_FITNESS)

    def evaluator(individual: classType) -> Any:
        """Evaluates an individual with a timeout."""
        assert len(holes) == 1, "Only 1 hole per function is supported now"
        result_queue = mp.Queue()
        eval_process = mp.Process(
            target=evaluate_individual,
            args=(individual, result_queue),
        )
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
    fitness_decorators = [
        "minimize_int",
        "minimize_float",
        "multi_minimize_float",
    ]

    if fun_name in metadata:
        used_decorators = [
            decorator for decorator in fitness_decorators
            if decorator in metadata[fun_name].keys()
        ]
        assert used_decorators, "No valid fitness decorators found."

        set_error_fitness(used_decorators)

        fitness_function = create_evaluator(
            ctx,
            ectx,
            term,
            fun_name,
            metadata,
            hole_names,
        )
        problem_type = (MultiObjectiveProblem if is_multiobjective(
            used_decorators, ) else SingleObjectiveProblem)
        target_fitness: float | list[float] = (
            0 if isinstance(problem_type, SingleObjectiveProblem) else 0
        )  # TODO: add support to maximize decorators

        return (
            problem_type(
                fitness_function=fitness_function,
                minimize=MINIMIZE_OBJECTIVE,
            ),
            target_fitness,
        )
    else:
        return (
            SingleObjectiveProblem(
                fitness_function=lambda x: 0,
                minimize=True,
            ),
            0,
        )


def get_grammar_components(
    ctx: TypingContext,
    ty: Type,
    fun_name: str,
    metadata: Metadata,
):
    grammar_nodes = gen_grammar_nodes(ctx, fun_name, metadata, [])

    assert len(grammar_nodes) > 0
    assert isinstance(
        ty,
        (BaseType, RefinedType),
    )  # TODO Synthesis: Support other types?
    hole_type_name = process_type_name(ty)
    grammar_nodes, starting_node = find_class_by_name(
        "t_" + hole_type_name,
        grammar_nodes,
        ty,
    )
    assert starting_node is not None, "Starting Node is None"
    grammar_nodes = build_control_flow_grammar_nodes(grammar_nodes)
    return grammar_nodes, starting_node


def create_grammar(
    holes: dict[str, tuple[Type, TypingContext]],
    fun_name: str,
    metadata: dict[str, Any],
):
    assert (len(
        holes,
    ) == 1), "More than one hole per function is not supported at the moment."
    hole_name = list(holes.keys())[0]
    ty, ctx = holes[hole_name]

    grammar_nodes, starting_node = get_grammar_components(
        ctx,
        ty,
        fun_name,
        metadata,
    )
    return extract_grammar(grammar_nodes, starting_node)


def random_search_synthesis(
    grammar: Grammar,
    problem: Problem,
    budget: int = 1000,
) -> Term:
    """Performs a synthesis procedure with Random Search."""
    max_depth = 5
    rep = TreeBasedRepresentation(grammar, max_depth)
    r = RandomSource(42)

    population = [rep.create_individual(r, max_depth) for _ in range(budget)]
    population_with_score = [(
        problem.evaluate(phenotype),
        phenotype.get_core(),
    ) for phenotype in population]
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
            gp_params["population_size"] - gp_params["n_elites"] -
            gp_params["novelty"],
        ],
    )


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
    representation: type = representations[representation_name](
        grammar,
        max_depth=gp_params["max_depth"],
    )

    tracker: ProgressTracker

    recorders = []
    if filename:
        csv_file_path = get_csv_file_path(
            filename,
            representation,
            seed,
            hole_name,
            config_name,
        )
        recorders.append(
            LazyCSVRecorder(
                csv_file_path,
                problem,
                only_record_best_individuals=gp_params[
                    "only_record_best_inds"],
            ), )
    if isinstance(problem, SingleObjectiveProblem):
        tracker = SingleObjectiveProgressTracker(
            problem,
            evaluator=SequentialEvaluator(),
            recorders=recorders,
        )
    else:
        tracker = MultiObjectiveProgressTracker(
            problem,
            evaluator=SequentialEvaluator(),
            recorders=recorders,
        )

    class UIBackendRecorder(SearchRecorder):

        def register(
            self,
            tracker: Any,
            individual: Individual,
            problem: Problem,
            is_best=False,
        ):
            ui.register(
                individual.get_phenotype().get_core(),
                individual.get_fitness(problem),
                tracker.get_elapsed_time(),
                is_best,
            )

    recorders.append(UIBackendRecorder())

    budget = TimeBudget(time=gp_params["timer_limit"])
    if target_fitness is not None:
        if isinstance(tracker, SingleObjectiveProgressTracker):
            search_budget = TargetFitness(target_fitness)
        elif isinstance(tracker, MultiObjectiveProgressTracker) and isinstance(
                target_fitness,
                list,
        ):
            search_budget = TargetMultiFitness(target_fitness)
        elif isinstance(tracker, MultiObjectiveProgressTracker) and isinstance(
                target_fitness,
            (float, int),
        ):
            search_budget = TargetMultiSameFitness(target_fitness)
        else:
            assert False
        budget = AnyOf(budget, search_budget)
    alg = GeneticProgramming(
        problem=problem,
        budget=budget,
        representation=representation,
        random=NativeRandomSource(seed),
        tracker=tracker,
        population_size=gp_params["population_size"],
        population_initializer=StandardInitializer(),
        step=create_gp_step(problem=problem, gp_params=gp_params),
    )

    ui.start(
        typing_ctx=None,
        evaluation_ctx=None,
        target_name=hole_name,
        target_type=None,
        budget=gengy_default_config["timer_limit"],
    )
    best: Individual = ui.wrapper(lambda: alg.search())
    print(
        f"Fitness of {best.get_fitness(problem)} by genotype: {best.genotype} with phenotype: {best.get_phenotype()}",
    )
    ui.end(best.get_phenotype().get_core(), best.get_fitness(problem))
    return best.get_phenotype().get_core()


def set_error_fitness(decorators):
    global ERROR_FITNESS
    if is_multiobjective(decorators):
        ERROR_FITNESS = [ERROR_NUMBER]
    else:
        ERROR_FITNESS = ERROR_NUMBER


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
        grammar,
        problem,
        filename,
        hole_name,
        target_fitness,
        synth_config,
        ui,
    )
    # synthesized_element = random_search_synthesis(grammar, problem)

    # Step 4 Substitute the synthesized element in the original program and return it.
    return synthesized_element, substitution(
        term,
        synthesized_element,
        hole_name,
    )


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
    assert len(program_holes) == len(
        targets, ), "No support for function with more than one hole"

    results = {}

    for name, holes_names in targets:
        hterm, term = synthesize_single_function(
            ctx,
            ectx,
            term,
            name,
            {h: v
             for h, v in program_holes.items() if h in holes_names},
            metadata,
            filename,
            synth_config,
            ui,
        )
        results[name] = hterm

    return term, results
