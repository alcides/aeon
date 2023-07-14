from __future__ import annotations

import os
from typing import Callable, Optional

from geneticengine.algorithms.gp.individual import Individual
from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.grammar import extract_grammar, Grammar
from geneticengine.core.problems import SingleObjectiveProblem
from geneticengine.core.representations.api import Representation

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import top
from aeon.core.types import Type
from aeon.synthesis_grammar.grammar import  get_holes_info, gen_grammar_nodes, get_grammar_node
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
        self.ctx = ctx
        self.p = p
        self.ty = ty
        self.ectx = ectx
        self.holes = get_holes_info(ctx, p, ty)


    def get_grammar(self) -> Optional[Grammar]:
        if len(self.holes) > 1:

            first_hole_name = next(iter(self.holes))
            hole_type, hole_ctx, synth_func_name = self.holes[first_hole_name]

            grammar_n = gen_grammar_nodes(hole_ctx, synth_func_name)

            assert len(grammar_n) > 0

            starting_node = get_grammar_node("t_" + hole_type.name, grammar_n)
            assert starting_node is not None, "Starting Node is None"

            grammar = extract_grammar(grammar_n, starting_node)
            #print("g: ", grammar)

            return grammar

        else:
            return None

    def fitness(self, individual) -> float:
        individual_term = individual.get_core()
        first_hole_name = next(iter(self.holes))
        nt = substitution(self.p, individual_term, first_hole_name)

        try:
            check_type_errors(self.ctx, nt, self.ty)
        except Exception as e:
            # add loguru traceback
            # print(f"Check for type errors failed: {e}")
            # traceback.print_exception(e)
            return 100000000

        try:
            fitness_eval_term = Var("fitness")
            nt_e = substitution(nt, fitness_eval_term, "main")
            result = eval(nt_e, self.ectx)

        except Exception as e:
            # add loguru traceback
            # print(f"Evaluation failed: {e}")
            # traceback.print_exception(e)
            result = 100000000
        return abs(result)

    def synthesize(self,grammar: Grammar,
                        representation:type,
                        max_depth: int,
                        number_of_generations: int,
                        population_size: int,
                        n_elites: int,
                        target_fitness: int,
                        timer_stop_criteria: bool,
                        timer_limit:int,
                        file_path: str | None,
                        seed:int = 123,) -> Individual:

        if file_path:
            file_name = os.path.basename(file_path)
            name_without_extension = os.path.splitext(file_name)[0]
            directory = f"csv/{name_without_extension}/{representation.__name__}"

            os.makedirs(directory, exist_ok=True)
            csv_file_path = f"{directory}/{name_without_extension}_{seed}.csv"
        else:
            csv_file_path = None

        alg = SimpleGP(
            seed=seed,
            grammar=grammar,
            representation = representation,
            problem=SingleObjectiveProblem(
                minimize=True,
                fitness_function=self.fitness,
            ),
            max_depth=max_depth,
            number_of_generations=number_of_generations,
            population_size=population_size,
            n_elites=n_elites,
            verbose=2,
            target_fitness=target_fitness,
            timer_stop_criteria=timer_stop_criteria,
            timer_limit=timer_limit,
            save_to_csv=csv_file_path,
        )
        best = alg.evolve()
        return best

