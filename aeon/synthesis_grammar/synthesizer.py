from __future__ import annotations

import os
import sys
from typing import Any
from typing import Callable

from geneticengine.algorithms.gp.individual import Individual
from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.grammar import extract_grammar, Grammar
from geneticengine.core.problems import MultiObjectiveProblem
from geneticengine.core.problems import Problem
from geneticengine.core.problems import SingleObjectiveProblem
from geneticengine.core.random.sources import RandomSource
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
from aeon.synthesis_grammar.grammar import gen_grammar_nodes, get_grammar_node
from aeon.synthesis_grammar.identification import get_holes_info, iterate_top_level
from aeon.synthesis_grammar.utils import fitness_function_name_for
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


class SynthesisError(Exception):
    pass


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
) -> Callable[[Individual], Any]:
    """Creates the fitness function for a given synthesis context."""

    program_template = substitution(program, Var(fitness_function_name), "main")

    def evaluator(individual: Individual) -> Any:
        """Evaluates an individual"""
        assert len(holes) == 1, "Only 1 hole per function is supported now"
        first_hole_name = holes[0]
        individual_term = individual.get_core()
        individual_term = ensure_anf(individual_term, 10000000)  # TODO: Global counter?
        new_program = substitution(program_template, individual_term, first_hole_name)

        try:
            check_type_errors(ctx, new_program, Top())
            return eval(new_program, ectx)
        except Exception as e:
            # if type_errors:
            #     print("TYPECHECKER", "-------------------------------")
            #     print("TYPECHECKER", "+     Type Checking Error     +")
            #     for error in type_errors:
            #         print("TYPECHECKER", "-------------------------------")
            #         print("TYPECHECKER", error)
            #     print("TYPECHECKER", "-------------------------------")
            #     log_type_errors(type_errors)
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
    fitness_function = create_evaluator(ctx, ectx, term, fitness_function_name, hole_names)
    is_multiobjective = fitness_function_type == BaseType("List")  # TODO: replace when merging polymorphic types
    if is_multiobjective:
        return MultiObjectiveProblem(fitness_function, [False])  # TODO: Repeat [False] for number of objectivos

    else:
        return SingleObjectiveProblem(fitness_function, False)


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
    return extract_grammar(grammar_nodes, starting_node)  # noqa: F821


def random_search_synthesis(grammar: Grammar, problem: Problem, budget: int = 1000) -> Term:
    """Performs a synthesis procedure with Random Search"""
    MAX_DEPTH = 5
    rep = TreeBasedRepresentation(grammar, MAX_DEPTH)
    r = RandomSource(42)

    population = [rep.create_individual(r, MAX_DEPTH) for _ in range(budget)]
    population_with_score = [(problem.evaluate(phenotype), phenotype.get_core()) for phenotype in population]
    return min(population_with_score)[0]


def geneticengine_synthesis(
    grammar: Grammar,
    problem: Problem,
    file_path: str | None,
    hole_name: str,
) -> Term:
    """Performs a synthesis procedure with GeneticEngine"""

    # TODO add information about hole name
    csv_file_path = get_csv_file_path(file_path, TreeBasedRepresentation, 123, hole_name)

    parent_selection = determine_parent_selection_type(problem)
    alg = SimpleGP(
        seed=123,
        grammar=grammar,
        representation=TreeBasedRepresentation,
        problem=problem,
        selection_method=parent_selection,
        max_depth=8,
        population_size=20,
        n_elites=1,
        verbose=2,
        target_fitness=0,
        probability_mutation=0.01,
        probability_crossover=0.9,
        timer_stop_criteria=True,
        timer_limit=60,
        save_to_csv=csv_file_path,
    )
    best: Individual = alg.evolve()
    return best.phenotype.get_core()


def synthesize_single_function(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    fun_name: str,
    holes: dict[str, tuple[Type, TypingContext]],
    filename: str,
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

    # Step 2.1 Get Hole Type.

    # Step 2.2 Create grammar object.
    grammar = create_grammar(holes, fun_name)

    # TODO Synthesis: This function (and its parent) should be parameterized with the type of search procedure to use (e.g., Random Search, Genetic Programming, others...)

    # Step 3 Synthesize an element
    # return geneticengine_synthesis(grammar, problem, filename)
    return random_search_synthesis(grammar, problem)


def synthesize(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    targets: list[tuple[str, list[str]]],
    filename: str | None = None,
) -> Term:
    """Synthesizes code for multiple functions, each with multiple holes."""
    # neste momento esta a permitir recursao
    program_holes = get_holes_info(
        ctx,
        term,
        top,
        targets,
    )

    for name, holes_names in targets:
        term = synthesize_single_function(
            ctx, ectx, term, name, {h: v for h, v in program_holes.items() if h in holes_names}, filename
        )
    return term
