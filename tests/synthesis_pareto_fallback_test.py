"""Feasible-candidate enumeration must rank more than the first answer."""

from types import SimpleNamespace

import pytest

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.api import InvalidIndividualException, Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.candidate_archive import CandidateArchive
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name
from tests.synthesis_specifications_test import solve


class RecordingUI(SilentSynthesisUI):
    def __init__(self):
        self.fronts = []

    def register_front(self, front, elapsed_time):
        self.fronts.append(list(front))


def archive_for(evaluate, flags=(True, False), budget=1):
    backend = SimpleNamespace(seed=0)
    name = Name("f", 0)
    goals = [Goal(flag, 1, name) for flag in flags]
    ui = RecordingUI()
    archive = CandidateArchive(backend, name, {name: {"goals": goals}}, evaluate, budget, ui)
    return archive, backend, ui


def test_later_improvements_replace_first_but_keep_incomparable_members():
    scores = {0: [5, 1], 1: [3, 2], 2: [4, 4], 3: [3, 2]}
    archive, backend, ui = archive_for(lambda t: scores[t.value])
    result = archive.search(iter(Literal(i, t_int) for i in range(4)), lambda _: True)
    assert {term.value for _, term in backend.pareto_front} == {1, 2}
    assert result.value in {1, 2}
    assert ui.fronts[-1] == backend.pareto_front
    assert len(ui.fronts[0]) == 1  # Earlier UI snapshots remain stable.


def test_invalid_scores_and_candidates_are_excluded_and_iterator_is_closed():
    closed = []
    evaluated = []

    def candidates():
        try:
            for i in range(5):
                yield Literal(i, t_int)
        finally:
            closed.append(True)

    def evaluate(term):
        evaluated.append(term.value)
        if term.value == 1:
            raise InvalidIndividualException()
        return [float("nan") if term.value == 2 else -term.value]

    archive, backend, _ = archive_for(evaluate, (True,))
    result = archive.search(candidates(), lambda t: t.value != 4)
    assert result == Literal(3, t_int)
    assert evaluated == [0, 1, 2, 3] and closed == [True]
    assert backend.pareto_front == [([-3], result)]


def test_budget_exhaustion_preserves_incumbent_and_next_run_clears_archive():
    archive, backend, _ = archive_for(lambda t: [t.value], (False,))

    def candidates():
        yield Literal(0, t_int)
        yield Literal(1, t_int)
        raise SynthesisNotSuccessful("search budget exhausted")

    assert archive.search(candidates(), lambda _: True) == Literal(1, t_int)
    name = Name("f", 0)
    fresh = CandidateArchive(backend, name, {}, lambda _: pytest.fail(), 0, SilentSynthesisUI())
    assert backend.pareto_front == []
    assert fresh.search(iter([Literal(2, t_int)]), lambda _: True) is None


class FiniteBackend(Synthesizer):
    supports_optimization = False
    supports_candidate_enumeration = True

    def computations(self, primitives):
        return {}

    def synthesize(self, *, validate, evaluate, fun_name, metadata, budget, ui, **kwargs):
        archive = CandidateArchive(self, fun_name, metadata, evaluate, budget, ui)
        return archive.search(iter(Literal(i, t_int) for i in range(5)), validate)


def test_minmax_cannot_trade_away_examples_properties_or_refinements():
    backend = FiniteBackend()
    result = solve(
        """
        @example(f 0 > 0)
        @maximize_int(f 0)
        def f (x:Int) : {v:Int | v < 4} := ?h;
        @property(3) def p (x:Int) : Bool := f x < 3;
    """,
        backend,
    )
    assert list(result.values()) == [Literal(2, t_int)]
    assert [term.value for _, term in backend.pareto_front] == [2]


@pytest.mark.parametrize("name", ["fta", "afta", "cata", "lta", "rl_mcts", "sygus", "polynomial"])
def test_real_backends_keep_multiple_tradeoffs(name):
    backend = make_synthesizer(name)
    if name in ("fta", "afta", "cata"):
        backend.rounds = 0
    if name == "rl_mcts":
        backend.max_depth = 0
    source = """
        @minimize_int(f 0)
        @maximize_int(f 0)
        def f (x:Int) : {v:Int | v >= 0 && v <= 1} := ?h;
    """
    if name == "lta":
        # LTA's literal states carry base types, so numeric bounds use the
        # runtime oracle; refined-literal inference is a separate limitation.
        source = source.replace("{v:Int | v >= 0 && v <= 1}", "Int")
        source = "@example(f 0 = 0 || f 0 = 1) " + source
        backend.max_depth = 0
    result = solve(source, backend, budget=3)
    assert all(t is not None for t in result.values())
    assert {tuple(scores[-2:]) for scores, _ in backend.pareto_front} == {(0.0, 0.0), (1.0, 1.0)}


@pytest.mark.parametrize("name", ["fta", "afta", "bustle_baseline", "contata", "arborist"])
def test_equal_example_vectors_do_not_hide_objective_tradeoffs(name):
    backend = make_synthesizer(name)
    if name == "contata":
        backend.max_size = 1
    if name == "arborist":
        backend.max_depth = 0
    if name in ("fta", "afta"):
        backend.rounds = 0
    result = solve(
        """
        @example(f 0 = 0)
        @minimize_int(f 1)
        @maximize_int(f 1)
        def f (x:{v:Int | v >= 0 && v <= 1}) : {v:Int | v >= 0 && v <= 1} := ?h;
    """,
        backend,
        budget=4,
    )
    assert all(t is not None for t in result.values())
    assert len(backend.pareto_front) == 2
    assert all(scores[0] == 0 for scores, _ in backend.pareto_front)


@pytest.mark.parametrize("name", ["smt", "polynomial"])
def test_solver_enumeration_blocks_programs_and_exhausts_finite_space(name):
    from time import monotonic
    from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt
    from aeon.synthesis.modules.polynomial import CertificateProblem, PolynomialConfig
    from aeon.synthesis.solver_problem import SolverClause, SolverHole, SolverProblem
    from aeon.synthesis.solver_z3 import enumerate_joint_z3

    symbol = Name("h", 0)
    call = LiquidApp(symbol, [LiquidLiteralInt(0)])
    lower = LiquidApp(Name(">=", 0), [call, LiquidLiteralInt(0)])
    upper = LiquidApp(Name("<=", 0), [call, LiquidLiteralInt(1)])
    problem = SolverProblem(
        (SolverHole(symbol, symbol, (), (), t_int),),
        (SolverClause((), LiquidLiteralBool(True), LiquidApp(Name("&&", 0), [lower, upper])),),
    )
    if name == "smt":
        candidates = enumerate_joint_z3(problem, 2000)
    else:
        candidates = CertificateProblem(problem, PolynomialConfig(), monotonic() + 2).candidates()
    results = list(candidates)
    assert {candidate.terms[0].value for candidate in results} == {0, 1}
    assert len(results) == 2  # Distinct certificates must not duplicate programs.


def test_structure_guided_continues_after_first_valid_recurrence():
    from tests.structure_guided_synthesis_test import LIST, solve_source
    from aeon.synthesis.modules.structure_guided import StructureGuidedSynthesizer
    from aeon.synthesis.modules.structure_guided.search import Config

    backend = StructureGuidedSynthesizer(Config(max_calls=1, max_added=1, max_base=0))
    _, _, backend = solve_source(
        LIST
        + """
        @example(f Chain.nil = Chain.nil)
        @minimize_int(7)
        @allow_recursion
        def f (xs:Chain) : Chain := ?h;
    """,
        backend,
    )
    assert backend.stats.candidates > 1
    assert [scores for scores, _ in backend.pareto_front] == [[0.0, 7.0]]


def test_single_smt_does_not_return_first_io_match_when_objectives_are_present():
    backend = make_synthesizer("smt")
    result = solve(
        """
        @example(f 0 = 0)
        @maximize_int(f 1)
        def f (x:Int) : Int := ?h;
    """,
        backend,
        budget=2,
    )
    assert all(term is not None for term in result.values())
    assert backend.pareto_front
