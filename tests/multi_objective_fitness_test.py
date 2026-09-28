"""Regression tests for issue #294.

Multi-objective fitness must be returned as the language's native ``Array`` type
(not the ``List`` ADT with a hardcoded, unresolved ``Name(..., -1)`` id), refined
so its length equals the number of objectives derived from the decorator's
argument list (one element per objective).

Fitness evaluation must unpack that Array into a flat ``list[float]`` whose
length matches ``minimize_flags_from_goals``, so Pareto search sees one
component per objective.
"""

from __future__ import annotations

from typing import Callable

import pytest

# Import ``tests.driver`` first: it pulls in ``aeon.decorators`` (and through it
# ``aeon.synthesis.decorators``) in the right order, avoiding the package's
# pre-existing import cycle when ``aeon.synthesis.decorators`` is imported first.
from tests.driver import check_and_return_core
from tests.synthesis_helpers import synthesize_holes_or_skip

from aeon.core.terms import Literal, Term
from aeon.core.types import Type, t_int
from aeon.decorators import Metadata
from aeon.synthesis.api import InvalidIndividualException, Synthesizer
from aeon.synthesis.decorators import multi_objective_type
from aeon.synthesis.fitness_eval import as_objective_vector
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisUI
from aeon.sugar.stypes import SRefinedType, STypeConstructor
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _array_base(ty: SRefinedType) -> STypeConstructor:
    assert isinstance(ty, SRefinedType), f"expected a refined type, got {type(ty).__name__}"
    base = ty.type
    assert isinstance(base, STypeConstructor)
    return base


def test_multi_objective_type_is_native_array():
    """The fitness type is the native ``Array`` constructor, never ``List``."""
    ty = multi_objective_type("Float", 3)
    base = _array_base(ty)
    assert base.name.name == "Array"
    assert base.name.name != "List"
    assert len(base.args) == 1
    assert isinstance(base.args[0], STypeConstructor)
    assert base.args[0].name.name == "Float"


def test_multi_objective_type_has_no_unresolved_name():
    """The old code returned ``Name("List", -1)``; the array constructor must
    not smuggle in that unresolved placeholder id."""
    ty = multi_objective_type("Int", 2)
    base = _array_base(ty)
    assert base.name.name == "Array"
    # The element type carries the canonical builtin id, not the -1 sentinel.
    assert base.args[0].name == STypeConstructor(base.args[0].name).name


def test_multi_objective_type_refines_by_objective_count():
    """The type carries a ``size v == N`` refinement, with N the objective count."""
    for n in (1, 2, 4):
        ty = multi_objective_type("Float", n)
        refinement = str(ty.refinement)
        assert "Array_size" in refinement
        assert f"{n}" in refinement


def test_multi_objective_element_type_tracks_decorator():
    assert _array_base(multi_objective_type("Float", 1)).args[0].name.name == "Float"
    assert _array_base(multi_objective_type("Int", 1)).args[0].name.name == "Int"


def test_multi_minimize_float_typechecks_against_native_array():
    """A fitness expression returning a native ``Array`` of exactly N elements
    typechecks against the refined fitness type, and a goal of length N is
    registered."""
    source = """
        import Array;
        @multi_minimize_float(native "[1.0, 2.0]", 2)
        def synth (i:Int) : Int := (?hole: Int)
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = [g for v in metadata.values() if isinstance(v, dict) for g in v.get("goals", [])]
    assert len(goals) == 1
    assert goals[0].minimize is True
    assert goals[0].length == 2
    assert [goals[0].minimize for _ in range(goals[0].length)] == [True, True]


def test_multi_minimize_int_typechecks_against_native_array():
    source = """
        import Array;
        @multi_minimize_int(native "[1, 2, 3]", 3)
        def synth (i:Int) : Int := (?hole: Int)
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = [g for v in metadata.values() if isinstance(v, dict) for g in v.get("goals", [])]
    assert len(goals) == 1
    assert goals[0].length == 3


def test_as_objective_vector_scalar_and_array():
    assert as_objective_vector(3.5, 1) == [3.5]
    assert as_objective_vector([1.0, 2.0], 2) == [1.0, 2.0]
    assert as_objective_vector((4, 5, 6), 3) == [4.0, 5.0, 6.0]
    with pytest.raises(InvalidIndividualException):
        as_objective_vector([1.0], 2)
    with pytest.raises(InvalidIndividualException):
        as_objective_vector("nope", 1)


class _RecordingSynthesizer(Synthesizer):
    """Evaluate fixed Int literals and record the multi-objective vectors."""

    seen_scores: list[list[float]]

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
        candidates = [Literal(0, t_int), Literal(1, t_int), Literal(2, t_int)]
        assert all(validate(c) for c in candidates)
        self.seen_scores = [evaluate(c) for c in candidates]
        return candidates[0]


def test_multi_minimize_float_evaluates_to_flat_objective_vector():
    """``@multi_minimize_float`` Array fitness expands to N floats per candidate."""
    source = """
        open Array;
        def to_float (x: Int) : Float := native "float(x)";
        def times2 (x: Float) : Float := x * 2.0;
        @multi_minimize_float(
            append (append (new{Float} unit) (to_float (synth 0))) (times2 (to_float (synth 0))),
            2
        )
        def synth (i:Int) : Int := (?hole: Int)
    """
    core, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    synth = _RecordingSynthesizer()
    synthesize_holes_or_skip(
        ctx,
        ectx,
        core,
        targets,
        metadata,
        synthesizer=synth,
        budget=5,
        ui=SilentSynthesisUI(),
    )
    assert synth.seen_scores == [[0.0, 0.0], [1.0, 2.0], [2.0, 4.0]]
