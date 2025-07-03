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
from geneticengine.problems import InvalidFitnessException
from geneticengine.problems import MultiObjectiveProblem, Problem, SingleObjectiveProblem
from geneticengine.representations.tree.treebased import TreeBasedRepresentation
from geneticengine.random.sources import NativeRandomSource
from geneticengine.representations.tree.initializations import MaxDepthDecider
from geneticengine.evaluation import SequentialEvaluator
from geneticengine.evaluation.tracker import ProgressTracker
from geneticengine.algorithms.random_search import RandomSearch
from geneticengine.algorithms.enumerative import EnumerativeSearch
from geneticengine.algorithms.gp.gp import GeneticProgramming
from geneticengine.algorithms.one_plus_one import OnePlusOne
from geneticengine.algorithms.hill_climbing import HC
from geneticengine.solutions import Individual
from geneticengine.evaluation.recorder import SearchRecorder


def create_problem(
    validate: Callable[[Term], bool],
    evaluate: Callable[[Term], list[float]],
    fun_name: Name,
    metadata: Metadata,
) -> Problem:
    fitness_decorators = ["minimize_int", "minimize_float", "multi_minimize_float"]
    used_decorators = [
        decorator for decorator in fitness_decorators if fun_name in metadata and decorator in metadata[fun_name].keys()
    ]
    if used_decorators:
        minimize_list = [True for _ in used_decorators]

        def fitness_fun(phenotype: Any) -> list[float]:
            p = phenotype.get_core()
            assert isinstance(p, Term)
            if not validate(p):
                raise InvalidFitnessException()
            return evaluate(p)

        return MultiObjectiveProblem(fitness_function=fitness_fun, minimize=minimize_list)
    else:
        return SingleObjectiveProblem(fitness_function=lambda _: 0.0, minimize=False, target=0.0)


class GESynthesizer(Synthesizer):
    def __init__(self, seed: int = 0, method: str = "enumerative"):
        self.seed = seed
        self.method = method

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
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        class UIBackendRecorder(SearchRecorder):
            def register(self, tracker: Any, individual: Individual, problem: Problem, is_best=False):
                ui.register(
                    individual.get_phenotype().get_core(),
                    individual.get_fitness(problem),
                    tracker.get_elapsed_time(),
                    is_best,
                )

        grammar = create_grammar(ctx, type, fun_name, metadata)
        problem = create_problem(validate, evaluate, fun_name, metadata)

        tracker = ProgressTracker(problem, evaluator=SequentialEvaluator(), recorders=[UIBackendRecorder()])

        representation = TreeBasedRepresentation(
            grammar, decider=MaxDepthDecider(NativeRandomSource(self.seed), grammar, max_depth=5)
        )

        match self.method:
            case "random_search":
                alg = RandomSearch(
                    problem=problem,
                    budget=TimeBudget(budget),
                    representation=representation,
                    random=NativeRandomSource(self.seed),
                    tracker=tracker,
                )
            case "enumerative":
                alg = EnumerativeSearch(
                    problem=problem,
                    budget=TimeBudget(budget),
                    grammar=grammar,
                    tracker=tracker,
                )
            case "genetic_programming":
                alg = GeneticProgramming(
                    problem=problem,
                    budget=TimeBudget(budget),
                    representation=representation,
                    random=NativeRandomSource(self.seed),
                    tracker=tracker,
                )
            case "hill_climbing":
                alg = HC(
                    problem=problem,
                    budget=TimeBudget(budget),
                    representation=representation,
                    random=NativeRandomSource(self.seed),
                    tracker=tracker,
                )
            case "one_plus_one":
                alg = OnePlusOne(
                    problem=problem,
                    budget=TimeBudget(budget),
                    representation=representation,
                    random=NativeRandomSource(self.seed),
                    tracker=tracker,
                )
            case _:
                assert False, f"Method {self.method} not available for synthesis."
        individuals = alg.search()
        match individuals:
            case None:
                return None
            case [ind, *_]:
                # TODO: handle multiple answers
                return ind.get_phenotype().get_core()
            case _:
                return None
