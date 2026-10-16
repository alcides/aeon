import pytest

from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.api import InvalidIndividualException, TimeoutInEvaluationException, SynthesisNotSuccessful
from aeon.synthesis.modules.synquid import synthesizer as module
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.synthesis.decorators import Goal


@pytest.mark.parametrize("error", [InvalidIndividualException, TimeoutInEvaluationException])
def test_synquid_continues_after_invalid_fitness(monkeypatch, error):
    candidates = [Literal(0, t_int), Literal(1, t_int)]
    monkeypatch.setattr(module, "iter_candidates_size_then_level", lambda *a, **kw: iter(candidates))
    observed = []

    def evaluate(term):
        observed.append(term.value)
        if term.value == 0:
            raise error()
        return [0.0]

    name = Name("f", 100)
    result = module.SynquidSynthesizer().synthesize(
        TypingContext(),
        t_int,
        lambda term: True,
        evaluate,
        name,
        {name: {"goals": [Goal(True, 1, name)]}},
        ui=SilentSynthesisUI(),
    )
    assert result == candidates[1]
    assert observed == [0, 1]


def test_all_invalid_fitness_returns_no_solution(monkeypatch):
    monkeypatch.setattr(module, "iter_candidates_size_then_level", lambda *a, **kw: iter([Literal(0, t_int)]))

    def evaluate(term):
        raise InvalidIndividualException()

    name = Name("f", 100)
    with pytest.raises(SynthesisNotSuccessful):
        module.SynquidSynthesizer().synthesize(
            TypingContext(),
            t_int,
            lambda term: True,
            evaluate,
            name,
            {name: {"goals": [Goal(True, 1, name)]}},
            ui=SilentSynthesisUI(),
        )
