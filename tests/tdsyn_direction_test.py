"""One-step backward and forward variants of the type-directed synthesizer.

`tdsyn_backward` and `tdsyn_forward` are demonstrative: they apply their
action exactly once to the hole and return the result — a complete candidate
when one validates, otherwise a partial term with fresh `?<fun>_goal_<i>`
subgoal holes — instead of searching. The backward step decomposes the goal
type; the forward step closes the goal with a variable of the goal's type or
introduces a `let v := <forward application> in ?goal` binding. `tdsyn` /
`tdsyn_enumerative` / `tdsyn_random` remain the search backends that combine
both actions.
"""

from __future__ import annotations

import pytest

from aeon.core.terms import Hole, Let, Literal, Var
from aeon.core.types import t_bool, t_int
from aeon.elaboration.context import build_typing_context
from aeon.lsp.server import SYNTHESIZERS
from aeon.prelude.prelude import typing_vars
from aeon.sugar.lifting import lift
from aeon.sugar.lowering import lower_to_core_context
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.identification import get_holes
from aeon.synthesis.modules.synthesizerfactory import (
    SynthesizerFamily,
    is_known_synthesizer,
    make_synthesizer,
    synthesizer_family,
    synthesizer_label,
)
from aeon.synthesis.modules.tdsyn import synthesizer as tdsyn_module
from aeon.synthesis.modules.tdsyn.actions import forward_step_candidates
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynOneStepSynthesizer, TDSynSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, fresh_hole
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm

DIRECTIONAL_IDS = ["tdsyn_backward", "tdsyn_forward"]

_loc = SynthesizedLocation("test")


# ---------------------------------------------------------------------------
# registration: ids, labels, families, LSP menu
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("backend", DIRECTIONAL_IDS)
def test_directional_backends_are_known(backend):
    assert is_known_synthesizer(backend)


def test_directional_backends_have_distinct_labels():
    assert synthesizer_label("tdsyn_backward") == "Type-directed step (backward)"
    assert synthesizer_label("tdsyn_forward") == "Type-directed step (forward)"


@pytest.mark.parametrize("backend", DIRECTIONAL_IDS)
def test_directional_backends_are_type_directed(backend):
    assert synthesizer_family(backend) == SynthesizerFamily.TYPE_DIRECTED


@pytest.mark.parametrize("backend", DIRECTIONAL_IDS)
def test_directional_backends_in_lsp_menu(backend):
    assert backend in SYNTHESIZERS


# ---------------------------------------------------------------------------
# make_synthesizer wiring
# ---------------------------------------------------------------------------


def test_make_synthesizer_backward():
    synth = make_synthesizer("tdsyn_backward")
    assert isinstance(synth, TDSynOneStepSynthesizer)
    assert synth.direction == "backward"


def test_make_synthesizer_forward():
    synth = make_synthesizer("tdsyn_forward")
    assert isinstance(synth, TDSynOneStepSynthesizer)
    assert synth.direction == "forward"


@pytest.mark.parametrize("backend", ["tdsyn", "tdsyn_enumerative", "tdsyn_random"])
def test_combined_backends_are_search_synthesizers(backend):
    assert isinstance(make_synthesizer(backend), TDSynSynthesizer)


# ---------------------------------------------------------------------------
# one-step semantics
# ---------------------------------------------------------------------------


def _prelude_ctx() -> TypingContext:
    return lower_to_core_context(build_typing_context(typing_vars))


def _one_step(direction, ctx, ty, validate):
    return TDSynOneStepSynthesizer(direction=direction).synthesize(
        ctx,
        ty,
        validate=validate,
        evaluate=lambda t: [],
        fun_name=Name("synth", 0),
        metadata={},
    )


def test_backward_step_returns_complete_candidate_when_valid():
    term = _one_step("backward", TypingContext(), t_int, validate=lambda t: True)
    assert isinstance(term, Literal)
    assert get_holes(term) == []


def test_backward_step_returns_partial_with_named_subgoals():
    # With every complete candidate rejected, one backward step returns the
    # first partial expansion, with distinct human-readable subgoal holes.
    term = _one_step("backward", _prelude_ctx(), t_int, validate=lambda t: False)
    holes = get_holes(term)
    assert len(holes) >= 1
    names = [h.pretty() for h in holes]
    assert len(set(names)) == len(names)
    assert all(name.startswith("synth_goal_") for name in names)


def test_forward_step_closes_goal_with_matching_variable():
    # A variable whose type already proves the goal closes it directly.
    ctx = _prelude_ctx().with_var(Name("b", 42), t_bool)
    term = _one_step("forward", ctx, t_bool, validate=lambda t: True)
    assert isinstance(term, Var)
    assert get_holes(term) == []


def test_forward_step_introduces_let_binding():
    # With every complete candidate rejected, one forward step introduces a
    # `let v := <forward application> in ?goal` binding, reopening the goal.
    ctx = _prelude_ctx().with_var(Name("b", 42), t_bool)
    term = _one_step("forward", ctx, t_bool, validate=lambda t: False)
    assert isinstance(term, Let)
    assert isinstance(term.body, Hole)
    names = [h.pretty() for h in get_holes(term)]
    assert len(set(names)) == len(names)
    assert all(name.startswith("synth_goal_") for name in names)


def test_forward_step_let_reopens_goal_with_bound_variable_in_scope():
    # Action-level check: each let candidate's goal hole keeps the goal type
    # and gains the let-bound variable in its context.
    ctx = _prelude_ctx().with_var(Name("b", 42), t_bool)
    _, typed_hole = fresh_hole(t_bool, ctx)
    let_candidates = [
        (t, holes) for t, holes in forward_step_candidates(typed_hole, lambda name: False) if isinstance(t, Let)
    ]
    assert let_candidates
    for let_term, new_holes in let_candidates:
        goal_hole = new_holes[-1]
        assert isinstance(goal_hole, TypedHole)
        assert goal_hole.expected_type == t_bool
        bound = dict(goal_hole.context.vars())
        assert let_term.var_name in bound


def test_forward_step_let_pretty_prints_with_binder_and_goal_hole():
    # The printed form (what the LSP inserts) must keep both the let binder
    # and the open goal hole.
    ctx = _prelude_ctx().with_var(Name("b", 42), t_bool)
    term = _one_step("forward", ctx, t_bool, validate=lambda t: False)
    printed = pretty_print_sterm(lift(term), top_level=False)
    assert printed.startswith("let v := ")
    assert "?synth_goal_" in printed


def test_forward_step_fails_without_scope_variables():
    # Forward builds terms from variables in scope; an empty context has none.
    with pytest.raises(SynthesisNotSuccessful):
        _one_step("forward", TypingContext(), t_int, validate=lambda t: True)


# ---------------------------------------------------------------------------
# each backend invokes only its own action, exactly once
# ---------------------------------------------------------------------------


def _record_one_step_actions(direction: str, monkeypatch) -> list[str]:
    calls: list[str] = []

    def fake_backward(hole, skip):
        calls.append("backward")
        return [(Literal(1, t_int, _loc), [])]

    def fake_forward_step(hole, skip):
        calls.append("forward_step")
        return [(Var(Name("x", 0), _loc), [])]

    monkeypatch.setattr(tdsyn_module, "backward_candidates", fake_backward)
    monkeypatch.setattr(tdsyn_module, "forward_step_candidates", fake_forward_step)
    _one_step(direction, TypingContext(), t_int, validate=lambda t: True)
    return calls


def test_backward_step_uses_only_backward_action(monkeypatch):
    assert _record_one_step_actions("backward", monkeypatch) == ["backward"]


def test_forward_step_uses_only_forward_step_action(monkeypatch):
    assert _record_one_step_actions("forward", monkeypatch) == ["forward_step"]


def test_search_expansion_still_runs_both_actions(monkeypatch):
    # Regression: the combined search synthesizer keeps using both actions.
    calls: list[str] = []

    def fake_backward(hole, skip):
        calls.append("backward")
        return []

    def fake_forward(hole, skip):
        calls.append("forward")
        return []

    monkeypatch.setattr(tdsyn_module, "backward_candidates", fake_backward)
    monkeypatch.setattr(tdsyn_module, "forward_candidates", fake_forward)
    hole_term, typed_hole = fresh_hole(t_int, TypingContext())
    partial = PartialAST(term=hole_term, holes=[typed_hole], depth=0)
    TDSynSynthesizer()._expand_hole(partial, typed_hole, lambda name: False)
    assert calls == ["backward", "forward"]
