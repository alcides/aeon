from __future__ import annotations

import os

from geneticengine.algorithms.gp.individual import Individual
from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.grammar import extract_grammar
from geneticengine.core.grammar import Grammar
from geneticengine.core.problems import MultiObjectiveProblem
from geneticengine.core.problems import SingleObjectiveProblem

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import BaseType
from aeon.core.types import top
from aeon.core.types import Type
from aeon.synthesis_grammar.fitness import get_holes_info_and_fitness_type
from aeon.synthesis_grammar.grammar import gen_grammar_nodes
from aeon.synthesis_grammar.grammar import get_grammar_node
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


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
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, p, ty)
        self.holes: dict[str, tuple[Type, TypingContext, str]] = holes
        self.fitness_type: BaseType = fitness_type

    def get_grammar(self) -> Grammar | None:
        if len(self.holes) > 1:

            first_hole_name = next(iter(self.holes))
            hole_type, hole_ctx, synth_func_name = self.holes[first_hole_name]

            grammar_n = gen_grammar_nodes(hole_ctx, synth_func_name)

            assert len(grammar_n) > 0
            assert isinstance(hole_type, BaseType)
            starting_node = get_grammar_node("t_" + hole_type.name, grammar_n)
            assert starting_node is not None, "Starting Node is None"

            grammar = extract_grammar(grammar_n, starting_node)
            # print("g: ", grammar)

            return grammar

        else:
            return None

    def evaluate_fitness(self, individual, minimize):
        individual_term = individual.get_core()
        first_hole_name = next(iter(self.holes))
        nt = substitution(self.p, individual_term, first_hole_name)
        exception_return = 100000000 if not isinstance(minimize, list) else [100000000 for _ in range(len(minimize))]

        try:
            check_type_errors(self.ctx, nt, self.ty)
        except Exception as e:
            # add loguru traceback
            # print(f"Check for type errors failed: {e}")
            # traceback.print_exception(e)
            return exception_return

        try:
            fitness_eval_term = Var("fitness")
            nt_e = substitution(nt, fitness_eval_term, "main")
            return eval(nt_e, self.ectx)
        except Exception as e:
            # add loguru traceback
            # print(f"Evaluation failed: {e}")
            # traceback.print_exception(e)
            return exception_return

    def get_problem_type(self, minimize: bool | list[bool]):
        if isinstance(minimize, bool):
            assert self.fitness_type == BaseType("Float")
            return SingleObjectiveProblem(
                minimize=minimize,
                fitness_function=lambda individual: self.evaluate_fitness(individual, minimize),
            )

        elif isinstance(minimize, list):
            assert self.fitness_type == BaseType("List")
            return MultiObjectiveProblem(
                minimize=minimize,
                fitness_function=lambda individual: self.evaluate_fitness(individual, minimize),
            )

    def synthesize(
        self,
        file_path: str | None,
        grammar: Grammar,
        representation: type,
        minimize: bool | list[bool],
        max_depth: int,
        population_size: int,
        n_elites: int,
        target_fitness: int,
        probability_mutation: float = 0.01,
        probability_crossover: float = 0.9,
        timer_stop_criteria: bool = True,
        timer_limit: int = 60,
        seed: int = 123,
    ) -> Individual:

        if file_path:
            file_name = os.path.basename(file_path)
            name_without_extension = os.path.splitext(file_name)[0]
            directory = f"csv/{name_without_extension}/{representation.__name__}"

            os.makedirs(directory, exist_ok=True)
            csv_file_path = f"{directory}/{name_without_extension}_{seed}.csv"
        else:
            csv_file_path = None

        problem = self.get_problem_type(minimize)
        parent_selection = ("lexicase",) if isinstance(problem, MultiObjectiveProblem) else ("tournament", 5)

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
        best = alg.evolve()
        return best
