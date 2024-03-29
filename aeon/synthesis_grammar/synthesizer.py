from __future__ import annotations

import builtins
import os
import sys
import time
from typing import Any
from typing import Callable

import configparser
import multiprocess as mp
from geneticengine.algorithms.gp.individual import Individual
from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.grammar import extract_grammar, Grammar
from geneticengine.core.problems import MultiObjectiveProblem
from geneticengine.core.problems import Problem
from geneticengine.core.problems import SingleObjectiveProblem
from geneticengine.core.random.sources import RandomSource
from geneticengine.core.representations.grammatical_evolution.dynamic_structured_ge import (
    DynamicStructuredGrammaticalEvolutionRepresentation,
)
from geneticengine.core.representations.grammatical_evolution.ge import (
    GrammaticalEvolutionRepresentation,
)
from geneticengine.core.representations.grammatical_evolution.structured_ge import (
    StructuredGrammaticalEvolutionRepresentation,
)
from geneticengine.core.representations.tree.treebased import TreeBasedRepresentation
from loguru import logger

from aeon.backend.evaluator import EvaluationContext
from aeon.backend.evaluator import eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Term, Literal, Var
from aeon.core.types import BaseType, Top
from aeon.core.types import Type
from aeon.core.types import top
from aeon.decorators import Metadata
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.program import Definition
from aeon.synthesis_grammar.grammar import (
    gen_grammar_nodes,
    get_grammar_node,
    classType,
)
from aeon.synthesis_grammar.identification import get_holes_info
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


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
    "max_depth": 8,
    "population_size": 30,
    "n_elites": 1,
    "verbose": 2,
    "target_fitness": 0,
    "probability_mutation": 0.01,
    "probability_crossover": 0.9,
    "timer_stop_criteria": True,
    "timer_limit": 60,
    "representation": "tree",
    "config_name": "DEFAULT",
}


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
    directory = os.path.join("csv", name_without_extension, representation.__name__)
    os.makedirs(directory, exist_ok=True)

    hole_suffix = f"_{hole_name}" if hole_name else ""
    csv_file_name = f"{name_without_extension}{hole_suffix}_{seed}_{config_name}.csv"

    return os.path.join(directory, csv_file_name)


def determine_parent_selection_type(problem):
    return ("lexicase",) if isinstance(problem, MultiObjectiveProblem) else ("tournament", 5)


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
    fun_name: str,
    metadata: Metadata,
    holes: list[str],
) -> Callable[[classType], Any]:
    """Creates the fitness function for a given synthesis context."""
    fitness_decorators = ["minimize_int", "minimize_float", "multi_minimize_float"]
    used_decorators = [decorator for decorator in fitness_decorators if decorator in metadata[fun_name]]
    assert used_decorators, "No fitness decorators used in metadata for function."

    objectives_list: list[Definition] = [
        objective for decorator in used_decorators for objective in metadata[fun_name][decorator]
    ]
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
            logger.info(f"Individual evaluation time: {end-start} ")

        except Exception as e:
            # import traceback
            # traceback.print_exc()
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


def problem_for_fitness_function(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    fun_name: str,
    metadata: Metadata,
    hole_names: list[str],
) -> Problem:
    """Creates a problem for a particular function, based on the name and type
    of its fitness function."""
    fitness_decorators = ["minimize_int", "minimize_float", "multi_minimize_float"]
    used_decorators = [decorator for decorator in fitness_decorators if decorator in metadata[fun_name].keys()]
    assert used_decorators, "No valid fitness decorators found."

    set_error_fitness(used_decorators)

    fitness_function = create_evaluator(ctx, ectx, term, fun_name, metadata, hole_names)
    problem_type = MultiObjectiveProblem if is_multiobjective(used_decorators) else SingleObjectiveProblem

    return problem_type(fitness_function=fitness_function, minimize=MINIMIZE_OBJECTIVE)


def get_grammar_components(ctx: TypingContext, ty: Type, fun_name: str, metadata: Metadata):
    grammar_nodes = gen_grammar_nodes(ctx, fun_name, metadata, [])

    assert len(grammar_nodes) > 0
    assert isinstance(ty, BaseType)  # TODO Synthesis: Support other types?
    starting_node = get_grammar_node("t_" + ty.name, grammar_nodes)
    assert starting_node is not None, "Starting Node is None"
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
    r = RandomSource(42)

    population = [rep.create_individual(r, max_depth) for _ in range(budget)]
    population_with_score = [(problem.evaluate(phenotype), phenotype.get_core()) for phenotype in population]
    return min(population_with_score, key=lambda x: x[0])[1]


def geneticengine_synthesis(
    grammar: Grammar,
    problem: Problem,
    filename: str | None,
    hole_name: str,
    gp_params: dict[str, Any] | None = None,
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
    representation: type = representations[representation_name]

    if filename:
        csv_file_path = get_csv_file_path(filename, representation, seed, hole_name, config_name)
        gp_params["save_to_csv"] = csv_file_path
        gp_params["only_record_best_inds"] = False

    parent_selection = determine_parent_selection_type(problem)

    alg = SimpleGP(
        grammar=grammar,
        representation=representation,
        problem=problem,
        selection_method=parent_selection,
        **gp_params,
    )

    best: Individual = alg.evolve()
    print(
        f"Fitness of {best.get_fitness(problem)} by genotype: {best.genotype} with phenotype: {best.get_phenotype()}",
    )
    return best.phenotype.get_core()


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
) -> Term:
    # Step 1 Create a Single or Multi-Objective Problem instance.

    problem = problem_for_fitness_function(
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
    synthesized_element = geneticengine_synthesis(grammar, problem, filename, hole_name, synth_config)
    # synthesized_element = random_search_synthesis(grammar, problem)

    # Step 4 Substitute the synthesized element in the original program and return it.
    return substitution(term, synthesized_element, hole_name)


def synthesize(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    targets: list[tuple[str, list[str]]],
    metadata: Metadata,
    filename: str | None = None,
    synth_config: dict[str, Any] | None = None,
) -> Term:
    """Synthesizes code for multiple functions, each with multiple holes."""
    program_holes = get_holes_info(
        ctx,
        term,
        top,
        targets,
    )
    assert len(program_holes) == len(targets), "No support for function with more than one hole"

    print("Starting synthesis...")
    for name, holes_names in targets:
        term = synthesize_single_function(
            ctx,
            ectx,
            term,
            name,
            {h: v for h, v in program_holes.items() if h in holes_names},
            metadata,
            filename,
            synth_config,
        )

    return term
