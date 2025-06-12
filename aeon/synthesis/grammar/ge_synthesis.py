from typing import Any, Callable

from aeon.typechecking.context import TypingContext

from aeon.core.types import Type
from aeon.core.terms import Term
from aeon.utils.name import Name


from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.api import Synthesizer

from aeon.decorators.api import Metadata

from aeon.synthesis.grammar.grammar_generation import create_grammar

from geneticengine.evaluation.budget import TimeBudget
from geneticengine.problems import MultiObjectiveProblem, Problem
from geneticengine.representations.tree.treebased import TreeBasedRepresentation
from geneticengine.random.sources import NativeRandomSource
from geneticengine.representations.tree.initializations import MaxDepthDecider
from geneticengine.evaluation import SequentialEvaluator
from geneticengine.evaluation.tracker import ProgressTracker
from geneticengine.algorithms.random_search import RandomSearch
from geneticengine.solutions import Individual
from geneticengine.evaluation.recorder import SearchRecorder


def create_problem(
    evaluate: Callable[[Term], list[float]],
    fun_name: Name,
    metadata: Metadata,
) -> Problem:
    fitness_decorators = ["minimize_int", "minimize_float", "multi_minimize_float"]
    used_decorators = [decorator for decorator in fitness_decorators if decorator in metadata[fun_name].keys()]
    minimize_list = [True for _ in used_decorators]

    def fitness_fun(phenotype: Any) -> list[float]:
        p = phenotype.get_core()
        assert isinstance(p, Term)
        return evaluate(p)

    return MultiObjectiveProblem(fitness_function=fitness_fun, minimize=minimize_list)


class GESynthesizer(Synthesizer):
    def __init__(self, seed: int = 0):
        self.seed = seed

    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> Term:
        class UIBackendRecorder(SearchRecorder):
            def register(self, tracker: Any, individual: Individual, problem: Problem, is_best=False):
                ui.register(
                    individual.get_phenotype().get_core(),
                    individual.get_fitness(problem),
                    tracker.get_elapsed_time(),
                    is_best,
                )

        grammar = create_grammar(ctx, type, fun_name, metadata)
        problem = create_problem(evaluate, fun_name, metadata)

        representation = TreeBasedRepresentation(
            grammar, decider=MaxDepthDecider(NativeRandomSource(self.seed), grammar, max_depth=5)
        )

        tracker = ProgressTracker(problem, evaluator=SequentialEvaluator(), recorders=[UIBackendRecorder()])

        alg = RandomSearch(
            problem=problem,
            budget=TimeBudget(budget),
            representation=representation,
            random=NativeRandomSource(self.seed),
            tracker=tracker,
        )
        individuals = alg.search()
        match individuals:
            case None:
                return None
            case [ind, *_]:
                # TODO: handle multiple answers
                return ind.get_phenotype().get_core()
            case _:
                assert False, f"Unknown result of search {individuals}"
