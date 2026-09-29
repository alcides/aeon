import pytest

from aeon.core.types import TypeConstructor
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.decorators import Goal
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.pareto import dominates, pick_pareto_member, update_pareto_front
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from tests.driver import check_and_return_core
from tests.synthesis_helpers import first_hole_term, synthesize_holes_or_skip

_INT = TypeConstructor(Name("Int", 0), [])


def test_dominates():
    assert dominates([1.0, 2.0], [2.0, 3.0], [True, True])
    assert not dominates([1.0, 2.0], [1.0, 2.0], [True, True])
    assert not dominates([1.0, 3.0], [2.0, 2.0], [True, True])


def test_update_pareto_front():
    front, added = update_pareto_front([], [1.0, 2.0], "a", [True, True])
    assert added
    assert front == [([1.0, 2.0], "a")]

    front, added = update_pareto_front(front, [2.0, 1.0], "b", [True, True])
    assert added
    assert len(front) == 2

    front, added = update_pareto_front(front, [0.5, 0.5], "c", [True, True])
    assert added
    assert front == [([0.5, 0.5], "c")]


def test_pick_pareto_member_is_seeded():
    front = [([2.0, 1.0], "b"), ([1.0, 2.0], "a")]
    assert pick_pareto_member(front, seed=0) == pick_pareto_member(front, seed=0)


def test_synquid_raises_when_no_valid_candidate():
    ctx = TypingContext()
    fun_name = Name("f", 0)
    metadata = {
        fun_name: {
            "goals": [Goal(minimize=True, length=1, function=Name("g", 0))],
            "synquid_max_candidates": 0,
        }
    }

    with pytest.raises(SynthesisNotSuccessful, match="SynquidSynthesizer: no valid candidate found within budget"):
        SynquidSynthesizer().synthesize(
            ctx,
            _INT,
            validate=lambda _: False,
            evaluate=lambda _: [1.0],
            fun_name=fun_name,
            metadata=metadata,
            budget=1.0,
        )


def test_synquid():
    source = """@minimize_int(func(25))
            def func (i:Int) : Int :=
                let a : Int := 10*i;
                (?hole: {x:Int | x >= (-45)} ) * i - a
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(
        ctx,
        core_ast_anf,
    )
    mapping = synthesize_holes_or_skip(
        ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer=SynquidSynthesizer(), budget=0.25
    )
    assert len(mapping) == 1
    first_hole_term(mapping)


def test_synquid_simple():
    source = """@minimize_int(1)
            def synth : Int := ?hole;
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(
        ctx,
        core_ast_anf,
    )
    mapping = synthesize_holes_or_skip(
        ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer=SynquidSynthesizer(), budget=0.25
    )
    assert len(mapping) > 0
    first_hole_term(mapping)
