"""One-step tactic backends of the type-directed synthesizer.

`tdsyn_backward` and the `forward_*` backends are demonstrative: they apply
their action exactly once to the hole and return the result — a complete
candidate when one validates, otherwise a partial term with fresh
`?<fun>_goal_<i>` subgoal holes — instead of searching. The backward step
decomposes the goal type; `forward_close` closes the goal with a variable of
the goal's type; the `forward_let_*` steps introduce a
`let v := <value> in ?goal` binding, one per term former (application,
if-then-else, type application, abstraction, type abstraction). `tdsyn` /
`tdsyn_enumerative` / `tdsyn_random` remain the search backends that combine
the full backward and forward actions.
"""

from __future__ import annotations

import pytest

from aeon.core.terms import Abstraction, Application, Hole, If, Literal, Rec, TypeAbstraction, TypeApplication, Var
from aeon.core.types import AbstractionType, TypePolymorphism, t_bool, t_int
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
from aeon.synthesis.modules.tdsyn.actions import forward_let_app_candidates
from aeon.synthesis.modules.tdsyn.synthesizer import ONE_STEP_ACTIONS, TDSynOneStepSynthesizer, TDSynSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, fresh_hole
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm

ONE_STEP_IDS = [
    "tdsyn_backward",
    "forward_close",
    "forward_let_app",
    "forward_let_if",
    "forward_let_tapp",
    "forward_let_abs",
    "forward_let_tabs",
]

_loc = SynthesizedLocation("test")


# ---------------------------------------------------------------------------
# registration: ids, labels, families, LSP menu
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("backend", ONE_STEP_IDS)
def test_one_step_backends_are_known(backend):
    assert is_known_synthesizer(backend)


def test_one_step_backends_have_distinct_labels():
    labels = [synthesizer_label(backend) for backend in ONE_STEP_IDS]
    assert len(set(labels)) == len(labels)
    assert synthesizer_label("tdsyn_backward") == "Type-directed step (backward)"
    assert synthesizer_label("forward_close") == "Forward step (close with a variable)"
    assert synthesizer_label("forward_let_app") == "Forward step (let: application)"
    assert synthesizer_label("forward_let_if") == "Forward step (let: if-then-else)"
    assert synthesizer_label("forward_let_tapp") == "Forward step (let: type application)"
    assert synthesizer_label("forward_let_abs") == "Forward step (let: abstraction)"
    assert synthesizer_label("forward_let_tabs") == "Forward step (let: type abstraction)"


@pytest.mark.parametrize("backend", ONE_STEP_IDS)
def test_one_step_backends_are_type_directed(backend):
    assert synthesizer_family(backend) == SynthesizerFamily.TYPE_DIRECTED


@pytest.mark.parametrize("backend", ONE_STEP_IDS)
def test_one_step_backends_in_lsp_menu(backend):
    assert backend in SYNTHESIZERS


def test_tdsyn_forward_id_removed():
    assert not is_known_synthesizer("tdsyn_forward")
    assert "tdsyn_forward" not in SYNTHESIZERS


# ---------------------------------------------------------------------------
# make_synthesizer wiring
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("backend", ONE_STEP_IDS)
def test_make_synthesizer_one_step(backend):
    synth = make_synthesizer(backend)
    assert isinstance(synth, TDSynOneStepSynthesizer)
    expected_action = "backward" if backend == "tdsyn_backward" else backend
    assert synth.action == expected_action
    assert synth.action in ONE_STEP_ACTIONS


@pytest.mark.parametrize("backend", ["tdsyn", "tdsyn_enumerative", "tdsyn_random"])
def test_combined_backends_are_search_synthesizers(backend):
    assert isinstance(make_synthesizer(backend), TDSynSynthesizer)


# ---------------------------------------------------------------------------
# one-step semantics
# ---------------------------------------------------------------------------


def _prelude_ctx() -> TypingContext:
    return lower_to_core_context(build_typing_context(typing_vars))


def _one_step(action, ctx, ty, validate):
    return TDSynOneStepSynthesizer(action=action).synthesize(
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


def test_forward_close_uses_matching_variable():
    ctx = _prelude_ctx().with_var(Name("b", 42), t_bool)
    term = _one_step("forward_close", ctx, t_bool, validate=lambda t: True)
    assert isinstance(term, Var)
    assert get_holes(term) == []


def test_forward_close_fails_without_matching_variable():
    with pytest.raises(SynthesisNotSuccessful):
        _one_step("forward_close", TypingContext(), t_int, validate=lambda t: True)


def _assert_let_step(term, value_cls):
    assert isinstance(term, Rec)
    assert isinstance(term.body, Hole)
    assert isinstance(term.var_value, value_cls)
    names = [h.pretty() for h in get_holes(term)]
    assert len(set(names)) == len(names)
    assert all(name.startswith("synth_goal_") for name in names)


def test_forward_let_app_binds_application():
    ctx = _prelude_ctx().with_var(Name("b", 42), t_bool)
    term = _one_step("forward_let_app", ctx, t_bool, validate=lambda t: False)
    _assert_let_step(term, Application)


def test_forward_let_app_fails_without_scope_variables():
    with pytest.raises(SynthesisNotSuccessful):
        _one_step("forward_let_app", TypingContext(), t_int, validate=lambda t: True)


def test_forward_let_if_binds_if_then_else():
    term = _one_step("forward_let_if", TypingContext(), t_int, validate=lambda t: False)
    _assert_let_step(term, If)
    # cond + then + else + reopened goal
    assert len(get_holes(term)) == 4


def test_forward_let_tapp_binds_type_application():
    term = _one_step("forward_let_tapp", _prelude_ctx(), t_int, validate=lambda t: False)
    _assert_let_step(term, TypeApplication)


def test_forward_let_abs_binds_abstraction():
    term = _one_step("forward_let_abs", TypingContext(), t_int, validate=lambda t: False)
    _assert_let_step(term, Abstraction)


def test_forward_let_tabs_binds_type_abstraction():
    term = _one_step("forward_let_tabs", TypingContext(), t_int, validate=lambda t: False)
    _assert_let_step(term, TypeAbstraction)


def test_forward_let_app_reopens_goal_with_bound_variable_in_scope():
    # Action-level check: each let candidate's goal hole keeps the goal type
    # and gains the let-bound variable in its context.
    ctx = _prelude_ctx().with_var(Name("b", 42), t_bool)
    _, typed_hole = fresh_hole(t_bool, ctx)
    candidates = forward_let_app_candidates(typed_hole, lambda name: False)
    assert candidates
    for let_term, new_holes in candidates:
        assert isinstance(let_term, Rec)
        goal_hole = new_holes[-1]
        assert isinstance(goal_hole, TypedHole)
        assert goal_hole.expected_type == t_bool
        bound = dict(goal_hole.context.vars())
        assert let_term.var_name in bound


def test_forward_let_abs_binds_function_typed_variable():
    # Action-level: v gets a function type into the goal's type.
    _, typed_hole = fresh_hole(t_int, TypingContext())
    let_term, new_holes = tdsyn_module.ONE_STEP_ACTIONS["forward_let_abs"](typed_hole, lambda name: False)[0]
    goal_hole = new_holes[-1]
    v_type = dict(goal_hole.context.vars())[let_term.var_name]
    assert isinstance(v_type, AbstractionType)
    assert v_type.type == t_int


def test_forward_let_tabs_binds_polymorphic_variable():
    _, typed_hole = fresh_hole(t_int, TypingContext())
    let_term, new_holes = tdsyn_module.ONE_STEP_ACTIONS["forward_let_tabs"](typed_hole, lambda name: False)[0]
    goal_hole = new_holes[-1]
    v_type = dict(goal_hole.context.vars())[let_term.var_name]
    assert isinstance(v_type, TypePolymorphism)
    assert v_type.body == t_int


def test_forward_let_app_pretty_prints_with_binder_and_goal_hole():
    # The printed form (what the LSP inserts) must keep both the let binder
    # and the open goal hole.
    ctx = _prelude_ctx().with_var(Name("b", 42), t_bool)
    term = _one_step("forward_let_app", ctx, t_bool, validate=lambda t: False)
    printed = pretty_print_sterm(lift(term), top_level=False)
    assert printed.startswith("let v : ")
    assert "?synth_goal_" in printed


# ---------------------------------------------------------------------------
# each backend invokes only its own action, exactly once
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("action", list(ONE_STEP_ACTIONS))
def test_one_step_invokes_only_its_action(action, monkeypatch):
    calls: list[str] = []

    def make_fake(name):
        def fake(hole, skip):
            calls.append(name)
            return [(Literal(1, t_int, _loc), [])]

        return fake

    for name in ONE_STEP_ACTIONS:
        monkeypatch.setitem(tdsyn_module.ONE_STEP_ACTIONS, name, make_fake(name))
    _one_step(action, TypingContext(), t_int, validate=lambda t: True)
    assert calls == [action]


def test_search_expansion_still_runs_both_actions(monkeypatch):
    # Regression: the combined search synthesizer keeps using both full actions.
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
