"""PBE must validate discovered solutions before expanding unrelated operators."""

from types import SimpleNamespace

import pytest

from aeon.core.terms import Literal, Var
from aeon.core.types import t_int, t_string
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.afta import AFTASynthesizer
from aeon.synthesis.modules.afta import pbe, synthesizer
from aeon.synthesis.modules.symetric.synthesizer import Component, base_key
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


@pytest.mark.parametrize("accept", [True, False])
@pytest.mark.parametrize("later_type", [t_string, t_int])
def test_pbe_validates_before_later_builder_exhausts_budget(monkeypatch, accept, later_type):
    clock = SimpleNamespace(now=0.0)
    timer = SimpleNamespace(time=lambda: clock.now)
    monkeypatch.setattr(pbe, "time", timer)
    monkeypatch.setattr(synthesizer, "time", timer)
    backend = AFTASynthesizer()
    function = Name("f", 0)
    candidate = Var(Name("upper", 1))
    key = base_key(t_string)
    good = Component(candidate.name, (key,), key, ())
    slow_key = base_key(later_type)
    slow = Component(Name("slow", 2), (key,), slow_key, ())
    # An unrelated return type may appear first in the imported context.
    builders = {key: [good, slow]} if slow_key == key else {slow_key: [slow], key: [good]}
    monkeypatch.setattr(backend, "_collect", lambda *args: (builders, {}))
    expanded = []

    def combinations(component, *args):
        expanded.append(component.name)
        if component == good:
            return [candidate]
        clock.now = 10.0
        return []

    monkeypatch.setattr(backend, "_combos", combinations)
    checked = []

    def validate(term):
        checked.append(term)
        return accept

    metadata = {
        function: {
            "io_examples": [(["a"], "A"), (["b"], "B")],
            "pbe_probe": lambda term, args: term.value if isinstance(term, Literal) else args[0].upper(),
        }
    }

    def run():
        return backend.synthesize(
            TypingContext(), t_string, validate, lambda _: [], function, metadata, budget=10, ui=SilentSynthesisUI()
        )

    if accept:
        assert run() == candidate
        assert expanded == [good.name]
    else:
        with pytest.raises(SynthesisNotSuccessful, match="no program consistent"):
            run()
        assert expanded == [good.name, slow.name]
    assert checked == [candidate]


def test_pbe_keeps_searching_for_better_objectives_across_builders(monkeypatch):
    backend = AFTASynthesizer(rounds=1)
    function = Name("f", 0)
    first, better = Var(Name("first", 1)), Var(Name("better", 2))
    key = base_key(t_string)
    components = [Component(term.name, (key,), key, ()) for term in (first, better)]
    monkeypatch.setattr(backend, "_collect", lambda *args: ({key: components}, {}))
    monkeypatch.setattr(backend, "_combos", lambda comp, *args: [Var(comp.name)])
    checked = []

    def validate(term):
        checked.append(term)
        return True

    result = backend.synthesize(
        TypingContext(),
        t_string,
        validate,
        lambda term: [2.0 if term == first else 1.0],
        function,
        {
            function: {
                "goals": [Goal(True, 1, function)],
                "io_examples": [(["a"], "A"), (["b"], "B")],
                "pbe_probe": lambda term, args: term.value if isinstance(term, Literal) else args[0].upper(),
            }
        },
        budget=10,
        ui=SilentSynthesisUI(),
    )
    assert result == better
    assert checked == [first, better]
