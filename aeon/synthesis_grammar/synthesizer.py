from __future__ import annotations

import os

from geneticengine.algorithms.gp.individual import Individual
from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.grammar import extract_grammar
from geneticengine.core.problems import MultiObjectiveProblem
from geneticengine.core.problems import SingleObjectiveProblem

from geneticengine.core.representations.tree.treebased import TreeBasedRepresentation

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Term, Let, Literal, Rec
from aeon.core.types import BaseType
from aeon.core.types import top
from aeon.core.types import Type
from aeon.sugar.program import Decorator
from aeon.synthesis_grammar.fitness import get_holes_info
from aeon.synthesis_grammar.grammar import gen_grammar_nodes
from aeon.synthesis_grammar.grammar import get_grammar_node
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


def is_valid_term_literal(term_literal: Term) -> bool:
    return (
        isinstance(term_literal, Literal)
        and term_literal.type == BaseType("Int")
        and isinstance(term_literal.value, int)
        and term_literal.value > 0
    )


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
        hole_data: tuple[Type, TypingContext, str], grammar_nodes: list[type]
    ) -> tuple[list[type], type]:
        hole_type, hole_ctx, synth_func_name = hole_data
        grammar_nodes = gen_grammar_nodes(hole_ctx, synth_func_name, grammar_nodes)

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
        exception_return: float | list[float] = (
            100000000 if not isinstance(minimize, list) else [100000000 for _ in range(len(minimize))]
        )

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
    def validate_fitness_term(fitness_term: Term, expected_type: BaseType) -> None:
        if (
            not isinstance(fitness_term, Let)
            or not isinstance(fitness_term.body, Rec)
            or not isinstance(fitness_term.body.var_type, BaseType)
            or fitness_term.body.var_type != expected_type
        ):
            raise ValueError(f"Invalid fitness term or type. Expected {expected_type}")

    def get_problem_type(self, synth_def_info: tuple[Term, list[Decorator]], program: Term):
        fitness_term = synth_def_info[0]

        # minimize_list = extract_minimize_list_from_decorators(synth_def_info[1])
        minimize_list = []
        assert len(minimize_list) > 0, "Minimize list cannot be empty"
        if len(minimize_list) == 1:
            self.validate_fitness_term(fitness_term, BaseType("Float"))
            return SingleObjectiveProblem(
                minimize=minimize_list[0],
                fitness_function=lambda individual: self.evaluate_fitness(
                    individual, fitness_term, minimize_list[0], program
                ),
            )

        elif len(minimize_list) > 1:
            self.validate_fitness_term(fitness_term, BaseType("List"))
            return MultiObjectiveProblem(
                minimize=minimize_list,
                fitness_function=lambda individual: self.evaluate_fitness(
                    individual, fitness_term, minimize_list, program
                ),
            )

    @staticmethod
    def get_csv_file_path(file_path: str, representation: type, seed: int, hole_name: str = "") -> str | None:
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
        return ("lexicase",) if isinstance(problem, MultiObjectiveProblem) else ("tournament", 5)

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
            csv_file_path = self.get_csv_file_path(file_path, representation, seed, hole_name)

            hole_data = self.holes[hole_name]
            grammar_nodes, starting_node = self.get_grammar_components(hole_data, grammar_nodes)
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
            program_to_synth = substitution(program_to_synth, best.genotype.get_core(), hole_name)

        return program_to_synth


def synthesize_single_function(
    ctx: TypingContext, ectx: EvaluationContext, term: Term, fun_name: str, holes: list[str]
) -> Term:
    # TODO: This function is not working yet
    return term


def synthesize(ctx: TypingContext, ectx: EvaluationContext, term: Term, targets=list[tuple[str, list[str]]]) -> Term:
    """Synthesizes code for multiple functions, each with multiple holes."""
    for name, holes in targets:
        term = synthesize_single_function(ctx, ectx, term, name, holes)
    return term
