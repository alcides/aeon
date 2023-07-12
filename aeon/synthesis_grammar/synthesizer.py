from __future__ import annotations

from typing import Callable
from geneticengine.core.grammar import extract_grammar

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import top
from aeon.core.types import Type
from aeon.synthesis_grammar.grammar import geneticengine, get_holes_info, gen_grammar_nodes, get_grammar_node
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors


class Synthesizer:
    def __init__(
        self,
        ctx: TypingContext,
        p: Term,
        ty: Type = top,
        ectx: EvaluationContext = EvaluationContext(),
        genetic_engine: Callable = geneticengine,
    ):
        self.ctx = ctx
        self.p = p
        self.ty = ty
        self.ectx = ectx
        self.genetic_engine = genetic_engine

        self.holes = get_holes_info(ctx, p, ty)

        if len(self.holes) > 1:

            first_hole_name = next(iter(self.holes))
            hole_type, hole_ctx, synth_func_name = self.holes[first_hole_name]

            grammar_n = gen_grammar_nodes(hole_ctx, synth_func_name)

            assert len(grammar_n) > 0

            starting_node = get_grammar_node("t_" + hole_type.name, grammar_n)
            assert starting_node is not None, "Starting Node is None"

            grammar = extract_grammar(grammar_n, starting_node)
            print("g: ", grammar)

            if self.genetic_engine is not None:
                self.genetic_engine(grammar, self.fitness)
        else:
            eval(p, ectx)

    def fitness(self, individual) -> float:
        individual_term = individual.get_core()

        first_hole_name = next(iter(self.holes))
        _, _, synth_func_name = self.holes[first_hole_name]

        nt = substitution(self.p, individual_term, first_hole_name)

        try:
            check_type_errors(self.ctx, nt, self.ty)
        except Exception as e:
            # print(f"Check for type errors failed: {e}")
            # traceback.print_exception(e)
            return 100000000

        try:
            fitness_eval_term = Var("fitness")
            nt_e = substitution(nt, fitness_eval_term, "main")
            result = eval(nt_e, self.ectx)

        except Exception as e:
            # print(f"Evaluation failed: {e}")
            # traceback.print_exception(e)
            result = 100000000
        return abs(result)
