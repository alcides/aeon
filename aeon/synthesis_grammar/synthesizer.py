from __future__ import annotations

import os
import sys
from typing import Callable

from geneticengine.algorithms.gp.individual import Individual
from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.problems import MultiObjectiveProblem
from geneticengine.core.problems import SingleObjectiveProblem
from geneticengine.core.problems import Problem
from geneticengine.core.grammar import extract_grammar

from geneticengine.core.representations.tree.treebased import TreeBasedRepresentation
from loguru import logger
from pyparsing import Any

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Term, Literal, Var
from aeon.core.types import BaseType, Top
from aeon.core.types import top
from aeon.core.types import Type
from aeon.sugar.program import Decorator
from aeon.synthesis.sources import SeededRandomSource
from aeon.synthesis_grammar.grammar import gen_grammar_nodes, get_grammar_node
from aeon.synthesis_grammar.identification import get_holes_info, iterate_top_level
from aeon.synthesis_grammar.utils import fitness_function_name_for
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


class SynthesisError(Exception):
    pass


def is_valid_term_literal(term_literal: Term) -> bool:
    return (isinstance(term_literal, Literal)
            and term_literal.type == BaseType("Int")
            and isinstance(term_literal.value, int) and term_literal.value > 0)


# TODO: Port
def get_csv_file_path(file_path: str,
                      representation: type,
                      seed: int,
                      hole_name: str = "") -> str | None:
    """
    Generate a csv file path based on provided file_path, representation and seed.

    Args:
        file_path (str): The original file path.
        representation (type): Representation type of the individual.
        seed (int): Seed for random number generation.

    Returns:
        str | None: Generated CSV file path or None if no file_path is provided.
    """
    if not file_path:
        return None

    file_name = os.path.basename(file_path)
    name_without_extension = os.path.splitext(file_name)[0]
    directory = f"csv/{name_without_extension}/{representation.__name__}"

    os.makedirs(directory, exist_ok=True)

    if hole_name:
        return f"{directory}/{name_without_extension}_{hole_name}_{seed}.csv"

    return f"{directory}/{name_without_extension}_{seed}.csv"


# TODO: port
def determine_parent_selection_type(problem):
    return ("lexicase", ) if isinstance(
        problem, MultiObjectiveProblem) else ("tournament", 5)


# TODO port
def synthesize_old(
    self,
    file_path: str | None,
    objectives: dict[str, tuple[Term, list[Decorator]]],
    max_depth: int = 8,
    population_size: int = 20,
    n_elites: int = 1,
    target_fitness: int = 0,
    representation: type = TreeBasedRepresentation,
    probability_mutation: float = 0.01,
    probability_crossover: float = 0.9,
    timer_stop_criteria: bool = True,
    timer_limit: int = 60,
    seed: int = 123,
) -> Term:
    """Synthesizes an individual based on the provided parameters and grammar.

    Args:
        file_path (str | None): Path to the file. If provided, results will be saved to a CSV file
        objectives (dict[str, tuple[Term, list[Decorator]]]): Determines if the objective is to minimize the fitness function
        max_depth (int): Maximum depth of the individual. (Defaults = 8)
        population_size (int): Size of the population. (Defaults = 20)
        n_elites (int): Number of elite individuals. (Defaults = 1)
        target_fitness (int): Target fitness value. Evolution stops when this is reached. (Defaults = 0)
        representation (type): Representation type of the individual. (Defaults = TreeBasedRepresentation)
        probability_mutation (float): Probability of mutation. (Defaults = 0.01)
        probability_crossover (float): Probability of crossover. (Defaults = 0.9)
        timer_stop_criteria (bool): If True, evolution stops based on a timer. (Defaults = True)
        timer_limit (int): Time limit in seconds for the evolution. (Defaults = 60)
        seed (int): Seed for random number generation. (Defaults = 123)

    Returns:
        Individual: The best synthesized individual.

    Raises:
        Exception: If there are issues with type checking or evaluation during synthesis.
    """

    # TODO Eduardo: Test
    assert len(objectives) + 1 == len(self.holes)

    ##############################################################################################################

    holes_names = list(self.holes.keys())
    grammar_nodes: list[type] = list()
    program_to_synth = self.p
    for i in range(len(objectives)):
        hole_name = holes_names[i]
        csv_file_path = self.get_csv_file_path(file_path, representation, seed,
                                               hole_name)

        hole_data = self.holes[hole_name]
        grammar_nodes, starting_node = self.get_grammar_components(
            hole_data, grammar_nodes)
        grammar = extract_grammar(grammar_nodes, starting_node)

        synth_objective = objectives[hole_data[2]]

        problem = self.get_problem_type(synth_objective, program_to_synth)
        parent_selection = self.determine_parent_selection_type(problem)

        alg = SimpleGP(
            seed=seed,
            grammar=grammar,
            representation=representation,
            problem=problem,
            selection_method=parent_selection,
            max_depth=max_depth,
            population_size=population_size,
            n_elites=n_elites,
            verbose=2,
            target_fitness=target_fitness,
            probability_mutation=probability_mutation,
            probability_crossover=probability_crossover,
            timer_stop_criteria=timer_stop_criteria,
            timer_limit=timer_limit,
            save_to_csv=csv_file_path,
        )
        best: Individual = alg.evolve()
        program_to_synth = substitution(program_to_synth,
                                        best.genotype.get_core(), hole_name)

    return program_to_synth


def create_evaluator(ctx: TypingContext, ectx: EvaluationContext,
                     program: Term, fitness_function_name: str,
                     holes: list[str]) -> Callable[[Individual], Any]:
    """Creates the fitness function for a given synthesis context."""

    program_template = substitution(program, Var(fitness_function_name),
                                    "main")

    def evaluator(individual: Individual) -> Any:
        """Evaluates an individual"""
        assert len(holes) == 1, "Only 1 hole per function is supported now"
        first_hole_name = holes[0]
        individual_term = individual.get_core()
        new_program = substitution(program_template, individual_term,
                                   first_hole_name)

        try:
            check_type_errors(ctx, new_program, Top())
            return eval(new_program, ectx)
        except Exception as e:
            logger.error("Failed in the fitness function:", e)
            return -(sys.maxsize - 1)

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
    fitness_function = create_evaluator(ctx, ectx, term, fitness_function_name,
                                        hole_names)
    is_multiobjective = fitness_function_type == BaseType(
        "List")  # TODO: replace when merging polymorphic types

    if is_multiobjective:
        return MultiObjectiveProblem(
            [False],
            fitness_function)  # TODO: Repeat [False] for number of objectivos
    else:
        return SingleObjectiveProblem(False, fitness_function)


def get_grammar_components(ctx: TypingContext, ty: Type, fun_name: str):
    grammar_nodes = gen_grammar_nodes(ctx, fun_name, [])

    assert len(grammar_nodes) > 0
    assert isinstance(ty, BaseType)  # TODO Synthesis: Support other types?
    starting_node = get_grammar_node("t_" + ty.name, grammar_nodes)
    assert starting_node is not None, "Starting Node is None"
    return grammar_nodes, starting_node


def create_grammar(holes: dict[str, tuple[Type, TypingContext]],
                   fun_name: str):
    assert len(
        holes
    ) == 1, "More than one hole per function is not supported at the moment."
    hole_name = list(holes.keys())[0]
    ty, ctx = holes[hole_name]

    grammar_nodes, starting_node = get_grammar_components(ctx, ty, fun_name)
    return extract_grammar(grammar_nodes, starting_node)  # noqa: F821


def synthesize_single_function(
        ctx: TypingContext, ectx: EvaluationContext, term: Term, fun_name: str,
        holes: dict[str, tuple[Type, TypingContext]]) -> Term:
    # TODO: This function is not working yet

    # Step 1.1 Get fitness function name, and type
    fitness_function_name = fitness_function_name_for(fun_name)
    candidate_function = [
        fun.var_type for fun in iterate_top_level(term)
        if fun.var_name == fitness_function_name
    ]
    if not candidate_function:
        raise SynthesisError(
            f"No fitness function name {fitness_function_name} to automatically synthesize function {fun_name}"
        )

    # Step 1.2 Create a Single or Multi-Objective Problem instance.
    problem_for_fitness_function(ctx, ectx, term, fitness_function_name,
                                 candidate_function[0], list(holes.keys()))

    # Step 2.1 Get Hole Type.

    # Step 2.2 Create grammar object.
    grammar = create_grammar(holes, fun_name)

    # Step 3 Synthesize an element
    MAX_DEPTH = 5
    rep = TreeBasedRepresentation(grammar, MAX_DEPTH)
    r = SeededRandomSource(42)
    phenotype = rep.create_individual(r, MAX_DEPTH)
    term = phenotype.get_core()

    # print(grammar)
    # print(objective)

    return term


def synthesize(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    targets=list[tuple[str, list[str]]],
    filename: str | None = None,
) -> Term:
    """Synthesizes code for multiple functions, each with multiple holes."""
    program_holes = get_holes_info(
        ctx,
        term,
        top,
    )

    for name, holes_names in targets:
        term = synthesize_single_function(
            ctx, ectx, term, name,
            {h: v
             for h, v in program_holes.items() if h in holes_names})
    return term
