from __future__ import annotations

import builtins
import os
import sys
from typing import Any
from typing import Callable

import configparser
import multiprocess as mp
from configparser import SectionProxy
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
from geneticengine.core.representations.grammatical_evolution.ge import GrammaticalEvolutionRepresentation
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
from aeon.frontend.anf_converter import ensure_anf
from aeon.synthesis_grammar.grammar import gen_grammar_nodes, get_grammar_node, classType
from aeon.synthesis_grammar.identification import get_holes_info, iterate_top_level
from aeon.synthesis_grammar.utils import fitness_function_name_for
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


class SynthesisError(Exception):
    pass


MINIMIZE_OBJECTIVE = True
ERROR_FITNESS = (sys.maxsize - 1) if MINIMIZE_OBJECTIVE else -(sys.maxsize - 1)

representations = {
    "tree": TreeBasedRepresentation,
    "ge": GrammaticalEvolutionRepresentation,
    "sge": StructuredGrammaticalEvolutionRepresentation,
    "dsge": DynamicStructuredGrammaticalEvolutionRepresentation,
}


def parse_config(gp_config: tuple[str, str] | None = None) -> SectionProxy:
    config = configparser.ConfigParser()
    if gp_config:
        gp_config_file = gp_config[0]
        config_section = gp_config[1]
    else:
        gp_config_file = "aeon/synthesis_grammar/gpconfig.gengy"
        config_section = "DEFAULT"
    config.read(gp_config_file)
    return config[config_section]


def is_valid_term_literal(term_literal: Term) -> bool:
    return (
        isinstance(term_literal, Literal)
        and term_literal.type == BaseType("Int")
        and isinstance(term_literal.value, int)
        and term_literal.value > 0
    )


def get_csv_file_path(file_path: str, representation: type, seed: int, hole_name: str = "") -> str | None:
    """
    Generate a CSV file path based on the provided file_path, representation, and seed.
    If file_path is empty, returns None.
    """
    if not file_path:
        return None

    file_name = os.path.basename(file_path)
    name_without_extension, _ = os.path.splitext(file_name)
    directory = os.path.join("csv", name_without_extension, representation.__name__)
    os.makedirs(directory, exist_ok=True)

    hole_suffix = f"_{hole_name}" if hole_name else ""
    csv_file_name = f"{name_without_extension}{hole_suffix}_{seed}.csv"

    return os.path.join(directory, csv_file_name)


def determine_parent_selection_type(problem):
    return ("lexicase",) if isinstance(problem, MultiObjectiveProblem) else ("tournament", 5)


def create_evaluator(
    ctx: TypingContext, ectx: EvaluationContext, program: Term, fitness_function_name: str, holes: list[str]
) -> Callable[[classType], Any]:
    """Creates the fitness function for a given synthesis context."""

    TIMEOUT_DURATION = 300  # seconds

    program_template = substitution(program, Var(fitness_function_name), "main")

    def evaluate_individual(individual: classType, result_queue: mp.Queue) -> Any:
        """Function to run in a separate process. Puts result in a Queue."""
        try:
            first_hole_name = holes[0]
            individual_term = individual.get_core()  # type: ignore
            individual_term = ensure_anf(individual_term, 10000000)
            new_program = substitution(program_template, individual_term, first_hole_name)
            check_type_errors(ctx, new_program, Top())
            result = eval(new_program, ectx)
        except Exception as e:
            logger.log("SYNTHESIZER", f"Failed in the fitness function: {e}")
            result = ERROR_FITNESS
        result_queue.put(result)

    def evaluator(individual: classType) -> Any:
        """Evaluates an individual with a timeout."""
        assert len(holes) == 1, "Only 1 hole per function is supported now"

        result_queue = mp.Queue()

        eval_process = mp.Process(target=evaluate_individual, args=(individual, result_queue))
        eval_process.start()

        eval_process.join(timeout=TIMEOUT_DURATION)

        if eval_process.is_alive():
            eval_process.terminate()
            eval_process.join()
            return ERROR_FITNESS
        else:
            return result_queue.get()

    return evaluator


def problem_for_fitness_function(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    fitness_function_name: str,
    fitness_function_type: Type,
    hole_names: list[str],
) -> Problem:
    """Creates a problem for a particular function, based on the name and type of its fitness function."""
    fitness_function = create_evaluator(ctx, ectx, term, fitness_function_name, hole_names)
    is_multiobjective = fitness_function_type == BaseType("List")  # TODO: replace when merging polymorphic types
    if is_multiobjective:
        return MultiObjectiveProblem(fitness_function=fitness_function, minimize=MINIMIZE_OBJECTIVE)

    else:
        return SingleObjectiveProblem(fitness_function=fitness_function, minimize=MINIMIZE_OBJECTIVE)


def get_grammar_components(ctx: TypingContext, ty: Type, fun_name: str):
    grammar_nodes = gen_grammar_nodes(ctx, fun_name, [])

    assert len(grammar_nodes) > 0
    assert isinstance(ty, BaseType)  # TODO Synthesis: Support other types?
    starting_node = get_grammar_node("t_" + ty.name, grammar_nodes)
    assert starting_node is not None, "Starting Node is None"
    return grammar_nodes, starting_node


def create_grammar(holes: dict[str, tuple[Type, TypingContext]], fun_name: str):
    assert len(holes) == 1, "More than one hole per function is not supported at the moment."
    hole_name = list(holes.keys())[0]
    ty, ctx = holes[hole_name]

    grammar_nodes, starting_node = get_grammar_components(ctx, ty, fun_name)
    return extract_grammar(grammar_nodes, starting_node)


def random_search_synthesis(grammar: Grammar, problem: Problem, budget: int = 1000) -> Term:
    """Performs a synthesis procedure with Random Search"""
    max_depth = 5
    rep = TreeBasedRepresentation(grammar, max_depth)
    r = RandomSource(42)

    population = [rep.create_individual(r, max_depth) for _ in range(budget)]
    population_with_score = [(problem.evaluate(phenotype), phenotype.get_core()) for phenotype in population]
    return min(population_with_score, key=lambda x: x[0])[1]


def geneticengine_synthesis(
    grammar: Grammar, problem: Problem, file_path: str | None, hole_name: str, gp_config: tuple[str, str] | None = None
) -> Term:
    """Performs a synthesis procedure with GeneticEngine"""
    config = parse_config(gp_config)
    representation_name = config.pop("representation")
    assert isinstance(representation_name, str)
    representation: type = representations[representation_name]

    csv_file_path = get_csv_file_path(file_path, representation, 123, hole_name)

    parent_selection = determine_parent_selection_type(problem)

    gp_params = {k: builtins.eval(v) for k, v in config.items()}  # Use eval with caution!

    alg = SimpleGP(
        grammar=grammar,
        representation=representation,
        problem=problem,
        selection_method=parent_selection,
        save_to_csv=csv_file_path,
        **gp_params,
    )

    best: Individual = alg.evolve()
    print(
        f"Fitness of {best.get_fitness(problem)} by genotype: {best.genotype} with phenotype: {best.get_phenotype()}",
    )
    return best.phenotype.get_core()


def synthesize_single_function(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    fun_name: str,
    holes: dict[str, tuple[Type, TypingContext]],
    filename: str,
    synth_config: tuple[str, str] | None = None,
) -> Term:
    # Step 1.1 Get fitness function name, and type
    fitness_function_name = fitness_function_name_for(fun_name)
    candidate_function = [fun.var_type for fun in iterate_top_level(term) if fun.var_name == fitness_function_name]
    if not candidate_function:
        raise SynthesisError(
            f"No fitness function name {fitness_function_name} to automatically synthesize function {fun_name}"
        )

    # Step 1.2 Create a Single or Multi-Objective Problem instance.
    problem = problem_for_fitness_function(
        ctx, ectx, term, fitness_function_name, candidate_function[0], list(holes.keys())
    )

    # Step 2 Create grammar object.
    grammar = create_grammar(holes, fun_name)

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
    filename: str,
    synth_config: tuple[str, str] | None = None,
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
            ctx, ectx, term, name, {h: v for h, v in program_holes.items() if h in holes_names}, filename, synth_config
        )

    return term
