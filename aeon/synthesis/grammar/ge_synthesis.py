from typing import Any, Callable, Sequence

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

from aeon.synthesis.decorators import Goal


def _knee_point_individual(
    individuals: Sequence[Individual | None],
    problem: Problem,
) -> Individual | None:
    """Pick a single individual from a Pareto front by knee-point (compromise) selection.

    All objectives are oriented toward minimization (maximize objectives are negated)
    and normalized to ``[0, 1]``. The chosen individual is the one whose normalized
    fitness vector has the smallest Euclidean distance to the utopia origin — the
    "elbow" where further gains in one objective require disproportionate sacrifice
    in another. Falls back to the lone valid candidate when only one exists, or to
    ``None`` when none are valid.
    """
    valid = [ind for ind in individuals if ind is not None and ind.get_fitness(problem).valid]
    if not valid:
        return None
    if len(valid) == 1:
        return valid[0]

    fits = [ind.get_fitness(problem).fitness_components for ind in valid]
    minimize = problem.minimize
    n_obj = len(minimize)
    # Orient each objective so smaller = better.
    oriented = [[(f[d] if minimize[d] else -f[d]) for d in range(n_obj)] for f in fits]
    # Per-dimension normalization to [0, 1]; dimensions with zero spread contribute 0.
    mins = [min(o[d] for o in oriented) for d in range(n_obj)]
    maxs = [max(o[d] for o in oriented) for d in range(n_obj)]
    spreads = [maxs[d] - mins[d] for d in range(n_obj)]

    def squared_distance_to_utopia(o: list[float]) -> float:
        total = 0.0
        for d in range(n_obj):
            if spreads[d] > 0:
                normalized = (o[d] - mins[d]) / spreads[d]
                total += normalized * normalized
        return total

    best_idx = min(range(len(valid)), key=lambda i: squared_distance_to_utopia(oriented[i]))
    return valid[best_idx]


def create_problem(
    validate: Callable[[Term], bool],
    evaluate: Callable[[Term], list[float]],
    fun_name: Name,
    metadata: Metadata,
) -> Problem:
    goals: list[Goal] = metadata.get(fun_name, {}).get("goals", [])
    minimize_list = [goal.minimize for goal in goals for _ in range(goal.length)]
    if minimize_list:

        def fitness_fun(phenotype: Any) -> list[float]:
            p = phenotype.get_core()
            assert isinstance(p, Term)
            if not validate(p):
                raise InvalidFitnessException()
            return evaluate(p)

        return MultiObjectiveProblem(fitness_function=fitness_fun, minimize=minimize_list)
    else:

        def single_fitness_fun(phenotype: Any) -> float:
            p = phenotype.get_core()
            assert isinstance(p, Term)
            if not validate(p):
                raise InvalidFitnessException()
            return 0.0

        return SingleObjectiveProblem(fitness_function=single_fitness_fun, minimize=False, target=0.0)


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
        output_value: Callable[[Term], object] | None = None,
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        counter = [0]  # individuals generated/evaluated so far

        class UIBackendRecorder(SearchRecorder):
            def register(self, tracker: Any, individual: Individual, problem: Problem, is_best=False):
                counter[0] += 1
                elapsed = tracker.get_elapsed_time()
                ui.register(
                    individual.get_phenotype().get_core(),
                    individual.get_fitness(problem),
                    elapsed,
                    is_best,
                )
                # Each individual is generated and then evaluated, so created and
                # assessed advance together for this population-based search.
                ui.progress(counter[0], counter[0], elapsed)

        grammar = create_grammar(ctx, type, fun_name, metadata)
        problem = create_problem(validate, evaluate, fun_name, metadata)

        tracker = ProgressTracker(problem, evaluator=SequentialEvaluator(), recorders=[UIBackendRecorder()])

        representation = TreeBasedRepresentation(
            grammar, decider=MaxDepthDecider(NativeRandomSource(self.seed), grammar, max_depth=5)
        )

        common_args = {
            "problem": problem,
            "budget": TimeBudget(budget),
            "tracker": tracker,
        }

        common_random_args = {"representation": representation, "random": NativeRandomSource(self.seed), **common_args}

        match self.method:
            case "random_search":
                alg = RandomSearch(**common_random_args)
            case "enumerative":
                alg = EnumerativeSearch(grammar=grammar, **common_args)
            case "genetic_programming":
                alg = GeneticProgramming(**common_random_args)
            case "hill_climbing":
                alg = HC(**common_random_args)
            case "one_plus_one":
                alg = OnePlusOne(**common_random_args)
            case _:
                assert False, f"Method {self.method} not available for synthesis."
        individuals = alg.search()
        if not individuals:
            return None
        chosen = _knee_point_individual(individuals, problem)
        if chosen is None:
            return None
        return chosen.get_phenotype().get_core()
