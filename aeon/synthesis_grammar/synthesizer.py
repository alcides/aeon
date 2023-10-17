from __future__ import annotations

import os
import sys
from typing import Callable

from geneticengine.algorithms.gp.individual import Individual
from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.grammar import extract_grammar
from geneticengine.core.problems import MultiObjectiveProblem
from geneticengine.core.problems import SingleObjectiveProblem
from geneticengine.core.problems import Problem

from geneticengine.core.representations.tree.treebased import TreeBasedRepresentation
from loguru import logger
from pyparsing import Any

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Term, Let, Literal, Rec, Var
from aeon.core.types import BaseType, Top
from aeon.core.types import top
from aeon.core.types import Type
from aeon.sugar.program import Decorator
from aeon.synthesis_grammar.fitness import get_holes_info
from aeon.synthesis_grammar.grammar import gen_grammar_nodes
from aeon.synthesis_grammar.grammar import get_grammar_node
from aeon.synthesis_grammar.identification import get_hole_type, iterate_top_level
from aeon.synthesis_grammar.utils import fitness_function_name_for
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


class SynthesisError(Exception):
    pass


def is_valid_term_literal(term_literal: Term) -> bool:
    return (isinstance(term_literal, Literal)
            and term_literal.type == BaseType("Int")
            and isinstance(term_literal.value, int) and term_literal.value > 0)


class Synthesizer:

    def __init__(
            self,
            ctx: TypingContext,
            p: Term,
            ty: Type = top,
            ectx: EvaluationContext = EvaluationContext(),
    ):
        self.ctx: TypingContext = ctx
        self.p: Term = p
        self.ty: Type = ty
        self.ectx: EvaluationContext = ectx
        holes = get_holes_info(ctx, p, ty)
        self.holes: dict[str, tuple[Type, TypingContext, str]] = holes

    @staticmethod
    def get_grammar_components(
            hole_data: tuple[Type, TypingContext, str],
            grammar_nodes: list[type]) -> tuple[list[type], type]:
        hole_type, hole_ctx, synth_func_name = hole_data
        grammar_nodes = gen_grammar_nodes(hole_ctx, synth_func_name,
                                          grammar_nodes)

        assert len(grammar_nodes) > 0
        assert isinstance(hole_type, BaseType)
        starting_node = get_grammar_node("t_" + hole_type.name, grammar_nodes)
        assert starting_node is not None, "Starting Node is None"

        # grammar = extract_grammar(grammar_nodes, starting_node)
        # print("g: ", grammar)

        return grammar_nodes, starting_node

    def evaluate_fitness(
        self,
        individual,
        fitness_term: Term,
        minimize: bool | list[bool],
        program: Term,
    ) -> float | list[float]:
        individual_term = individual.get_core()
        first_hole_name = next(iter(self.holes))
        nt = substitution(program, individual_term, first_hole_name)
        exception_return: float | list[float] = (100000000 if not isinstance(
            minimize, list) else [100000000 for _ in range(len(minimize))])

        try:
            check_type_errors(self.ctx, nt, self.ty)
        except Exception:
            # add loguru traceback
            # print(f"Check for type errors failed: {e}")
            # traceback.print_exception(e)
            return exception_return

        try:
            fitness_eval_term = fitness_term
            nt_e = substitution(nt, fitness_eval_term, "main")
            # print(nt_e)
            return eval(nt_e, self.ectx)
        except Exception:
            # add loguru traceback
            # print(f"Evaluation failed: {e}")
            # traceback.print_exception(e)
            return exception_return

    @staticmethod
    def validate_fitness_term(fitness_term: Term,
                              expected_type: BaseType) -> None:
        if (not isinstance(fitness_term, Let)
                or not isinstance(fitness_term.body, Rec)
                or not isinstance(fitness_term.body.var_type, BaseType)
                or fitness_term.body.var_type != expected_type):
            raise ValueError(
                f"Invalid fitness term or type. Expected {expected_type}")

    def get_problem_type(self, synth_def_info: tuple[Term, list[Decorator]],
                         program: Term):
        fitness_term = synth_def_info[0]

        # minimize_list = extract_minimize_list_from_decorators(synth_def_info[1])
        minimize_list: list[bool] = []
        assert len(minimize_list) > 0, "Minimize list cannot be empty"
        if len(minimize_list) == 1:
            self.validate_fitness_term(fitness_term, BaseType("Float"))
            return SingleObjectiveProblem(
                minimize=minimize_list[0],
                fitness_function=lambda individual: self.evaluate_fitness(
                    individual, fitness_term, minimize_list[0], program),
            )

        elif len(minimize_list) > 1:
            self.validate_fitness_term(fitness_term, BaseType("List"))
            return MultiObjectiveProblem(
                minimize=minimize_list,
                fitness_function=lambda individual: self.evaluate_fitness(
                    individual, fitness_term, minimize_list, program),
            )

    @staticmethod
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

    @staticmethod
    def determine_parent_selection_type(problem):
        return ("lexicase", ) if isinstance(
            problem, MultiObjectiveProblem) else ("tournament", 5)

    def synthesize(
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
            csv_file_path = self.get_csv_file_path(file_path, representation,
                                                   seed, hole_name)

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
                                            best.genotype.get_core(),
                                            hole_name)

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


def synthesize_single_function(ctx: TypingContext, ectx: EvaluationContext,
                               term: Term, fun_name: str,
                               hole_names: list[str]) -> Term:
    # TODO: This function is not working yet

    # Step 1. Get fitness function
    fitness_function_name = fitness_function_name_for(fun_name)
    candidate_function = [
        fun.var_type for fun in iterate_top_level(term)
        if fun.name == fitness_function_name
    ]
    if not candidate_function:
        raise SynthesisError(
            f"No fitness function name {fitness_function_name} to automatically synthesize function {fun_name}"
        )

    fitness_function_type = candidate_function[0]
    fitness_function = create_evaluator(ctx, ectx, term, fitness_function_name,
                                        hole_names)

    is_multiobjective = fitness_function_type == BaseType(
        "List")  # TODO: replace when merging polymorphic types

    objective: Problem
    if is_multiobjective:
        objective = MultiObjectiveProblem(
            [False],
            fitness_function)  # TODO: Repeat [False] for number of objectivos
    else:
        objective = SingleObjectiveProblem(False, fitness_function)

    # Step 2. Get Hole Type.
    holes = [(h, get_hole_type(ctx, h, term)) for h in hole_names]

    print(holes)
    print(objective)

    return term


def synthesize(
    ctx: TypingContext,
    ectx: EvaluationContext,
    term: Term,
    targets=list[tuple[str, list[str]]],
    filename: str | None = None,
) -> Term:
    """Synthesizes code for multiple functions, each with multiple holes."""
    for name, holes in targets:
        term = synthesize_single_function(ctx, ectx, term, name, holes)
    return term
