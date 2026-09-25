"""Semantics specific to grammar-enumerative synthesis."""

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules import enumerative
from aeon.synthesis.modules.enumerative import EnumerativeSynthesizer, _dominates, _update_pareto_front
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _install_candidates(monkeypatch, candidates):
    monkeypatch.setattr(enumerative, "iter_candidates", lambda *_args, **_kwargs: iter(candidates))


def test_factory_uses_native_enumerator():
    assert isinstance(make_synthesizer("enumerative"), EnumerativeSynthesizer)


def test_pareto_helpers_respect_mixed_objective_directions():
    assert _dominates([1.0, 9.0], [2.0, 8.0], [True, False])
    assert not _dominates([1.0, 7.0], [2.0, 8.0], [True, False])

    a = Literal(1, t_int)
    b = Literal(2, t_int)
    c = Literal(3, t_int)
    front, added = _update_pareto_front([], [1.0, 7.0], a, [True, False])
    assert added
    front, added = _update_pareto_front(front, [2.0, 8.0], b, [True, False])
    assert added and [candidate for _, candidate in front] == [a, b]
    front, added = _update_pareto_front(front, [0.0, 9.0], c, [True, False])
    assert added and front == [([0.0, 9.0], c)]


def test_without_objectives_returns_first_valid_candidate_without_fitness(monkeypatch):
    candidates = [Literal(0, t_int), Literal(1, t_int), Literal(2, t_int)]
    _install_candidates(monkeypatch, candidates)
    validated = []

    def validate(candidate):
        validated.append(candidate)
        return candidate.value == 1

    def must_not_evaluate(_candidate):
        raise AssertionError("objective evaluation is not needed when there are no objectives")

    result = EnumerativeSynthesizer().synthesize(
        TypingContext(),
        t_int,
        validate,
        must_not_evaluate,
        Name("f", 0),
        {},
        budget=100,
        ui=SilentSynthesisUI(),
    )

    assert result == candidates[1]
    assert validated == candidates[:2]


def test_with_objectives_runs_to_timeout_and_randomly_selects_from_front(monkeypatch):
    candidates = [Literal(0, t_int), Literal(1, t_int), Literal(2, t_int)]
    _install_candidates(monkeypatch, candidates)

    # One timestamp for search start, then one after each fully evaluated
    # candidate.  The third candidate crosses the budget.
    times = iter([0.0, 0.0, 0.0, 2.0])
    monkeypatch.setattr(enumerative, "monotonic", lambda: next(times))

    evaluated = []
    scores = {0: [0.0, 0.0], 1: [1.0, 1.0], 2: [2.0, 2.0]}

    def evaluate(candidate):
        evaluated.append(candidate)
        return scores[candidate.value]

    chosen_fronts = []

    class _Chooser:
        def choice(self, front):
            chosen_fronts.append(front)
            return front[1]

    seeds = []

    def random_with_seed(seed):
        seeds.append(seed)
        return _Chooser()

    monkeypatch.setattr(enumerative.random, "Random", random_with_seed)
    function = Name("f", 0)
    metadata = {
        function: {
            "goals": [
                Goal(minimize=True, length=1, function=Name("min", 0)),
                Goal(minimize=False, length=1, function=Name("max", 0)),
            ]
        }
    }

    result = EnumerativeSynthesizer(seed=17).synthesize(
        TypingContext(),
        t_int,
        lambda _candidate: True,
        evaluate,
        function,
        metadata,
        budget=1,
        ui=SilentSynthesisUI(),
    )

    assert evaluated == candidates
    assert seeds == [17]
    assert [candidate for _, candidate in chosen_fronts[0]] == candidates
    assert result == candidates[1]
