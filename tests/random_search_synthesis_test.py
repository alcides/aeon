"""Semantics specific to native random-search synthesis."""

import random

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules import native_search, random_search
from aeon.synthesis.modules.random_search import RandomSearchSynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _install_candidates(monkeypatch, candidates):
    monkeypatch.setattr(
        random_search,
        "iter_random_candidates",
        lambda *_args, **_kwargs: iter(candidates),
    )


def test_factory_uses_native_random_search():
    assert isinstance(make_synthesizer("random_search"), RandomSearchSynthesizer)


def test_without_objectives_returns_first_valid_candidate_without_fitness(monkeypatch):
    candidates = [Literal(0, t_int), Literal(1, t_int), Literal(2, t_int)]
    _install_candidates(monkeypatch, candidates)
    validated = []

    def validate(candidate):
        validated.append(candidate)
        return candidate.value == 1

    def must_not_evaluate(_candidate):
        raise AssertionError("objective evaluation is not needed when there are no objectives")

    result = RandomSearchSynthesizer().synthesize(
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

    times = iter([0.0, 0.0, 0.0, 2.0])
    monkeypatch.setattr(native_search, "monotonic", lambda: next(times))

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

    monkeypatch.setattr(native_search.random, "Random", random_with_seed)
    function = Name("f", 0)
    metadata = {
        function: {
            "goals": [
                Goal(minimize=True, length=1, function=Name("min", 0)),
                Goal(minimize=False, length=1, function=Name("max", 0)),
            ]
        }
    }

    result = RandomSearchSynthesizer(seed=17).synthesize(
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
    assert seeds[-1] == 17
    assert [candidate for _, candidate in chosen_fronts[0]] == candidates
    assert result == candidates[1]


def test_sample_one_prefers_closed_expansions(monkeypatch):
    """Closed expansions (literals/vars) beat open ones when both exist."""
    closed = Literal(1, t_int)
    open_partial_term = Literal(2, t_int)
    from aeon.synthesis.modules.tdsyn.worklist import PartialAST, fresh_hole
    from aeon.core.types import t_bool

    hole_term, typed = fresh_hole(t_int, TypingContext())
    initial = PartialAST(hole_term, [typed], 0)

    closed_opt = PartialAST(closed, [], 1)
    _, open_hole = fresh_hole(t_bool, TypingContext())
    open_opt = PartialAST(open_partial_term, [open_hole], 1)

    monkeypatch.setattr(native_search, "literal_completions", lambda _partial: [])
    monkeypatch.setattr(
        native_search,
        "expansions_for_hole",
        lambda *_args, **_kwargs: [open_opt, closed_opt],
    )

    expansion_picks = []

    class _Rng(random.Random):
        def choice(self, seq):
            seq = list(seq)
            if seq and isinstance(seq[0], PartialAST):
                expansion_picks.append(seq)
            return seq[0]

    result = native_search.sample_one(initial, lambda _n: False, _Rng(0), max_depth=5)
    assert result == closed
    assert expansion_picks and all(opt.holes == [] for opt in expansion_picks[0])
