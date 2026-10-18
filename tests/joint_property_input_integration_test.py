"""Keep the validated PBT input API when combining joint synthesis changes."""

from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.pbt import runner
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def test_single_target_wrapper_forwards_input_validation_options(monkeypatch):
    observed = {}

    def collect(*args, **kwargs):
        observed.update(kwargs)
        return []

    monkeypatch.setattr(runner, "property_corpora_for_targets", collect)
    target = Name("f", 17)
    evaluation_ctx = EvaluationContext({})
    assert (
        runner.property_corpora_for_target(
            TypingContext(),
            Literal(0, t_int),
            {},
            target,
            {target},
            input_synthesizers=("smt",),
            evaluation_ctx=evaluation_ctx,
        )
        == []
    )
    assert observed["input_synthesizers"] == ("smt",)
    assert observed["evaluation_ctx"] is evaluation_ctx
