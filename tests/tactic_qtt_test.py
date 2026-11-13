"""Every tactic transition checks QTT through its shared TacticState."""

import pytest

from aeon.core.liquid import LiquidApp, LiquidLiteralBool
from aeon.core.multiplicity import M0, M1
from aeon.core.terms import Abstraction, Annotation, Application, Hole, If, Literal, Var
from aeon.core.types import AbstractionType, RefinedType, t_bool, t_int
from aeon.synthesis.qtt import QTTValidator
from aeon.synthesis.tactics.assumption import tactic_assumption
from aeon.synthesis.tactics.builtin import tactic_apply_question, tactic_constructor
from aeon.synthesis.tactics.by_cases import tactic_by_cases
from aeon.synthesis.tactics.choose_literal import tactic_choose_literal
from aeon.synthesis.tactics.explicit_synth import ExplicitTacticSynthesizer
from aeon.synthesis.tactics.holes import collect_hole_judgments
from aeon.synthesis.tactics.inst import tactic_inst
from aeon.synthesis.tactics.split import tactic_split
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from tests.tactic_synth_test import _prelude_ctx
from aeon.core.parser import parse_type


X, Y, H = Name("x", 1), Name("y", 2), Name("h", 3)


def linear_state():
    return TacticState(TypingContext(), Abstraction(X, Hole(H)), AbstractionType(X, t_int, t_int, multiplicity=M1))


def test_state_defers_missing_uses_until_holes_close_without_mutating_parent():
    state = linear_state()
    assert state.qtt_feasible()
    assert state.transition(Abstraction(X, Literal(0, t_int))) is None
    out = state.transition(Abstraction(X, Var(X)))
    assert out is not None and out.qtt_feasible()
    assert isinstance(state.term.body, Hole)


def test_state_checks_branch_usage():
    state = linear_state()
    assert state.transition(Abstraction(X, If(Literal(True, t_bool), Var(X), Var(X)))) is not None
    assert state.transition(Abstraction(X, If(Literal(True, t_bool), Var(X), Literal(0, t_int)))) is None


@pytest.mark.parametrize("tactic", [tactic_assumption, tactic_apply_question])
def test_variable_tactics_skip_erased_hypothesis(tactic):
    typ = AbstractionType(X, t_int, AbstractionType(Y, t_int, t_int, multiplicity=M1), multiplicity=M0)
    state = TacticState(TypingContext(), Abstraction(X, Abstraction(Y, Hole(H))), typ)
    out = tactic(state, H)
    assert out is not None
    assert out.term.body.body == Var(Y)


def test_constructor_preserves_linear_introduction():
    typ = AbstractionType(X, t_int, t_int, multiplicity=M1)
    state = TacticState(TypingContext(), Hole(H), typ)
    out = tactic_constructor(state, H)
    assert out is not None and out.qtt_feasible()
    body_hole = next(iter(collect_hole_judgments(out.ctx, out.term, out.goal)))
    assert tactic_choose_literal(out, body_hole) is None
    assert tactic_assumption(out, body_hole) is not None


def test_constructor_skips_erased_function():
    arrow = AbstractionType(Name("arg", 4), t_int, t_int)
    typ = AbstractionType(X, arrow, AbstractionType(Y, arrow, t_int), multiplicity=M0)
    state = TacticState(TypingContext(), Abstraction(X, Abstraction(Y, Hole(H))), typ)
    out = tactic_constructor(state, H)
    assert out is not None
    assert out.term.body.body.fun == Var(Y)


def test_by_cases_skips_erased_condition():
    typ = AbstractionType(X, t_bool, AbstractionType(Y, t_bool, t_int), multiplicity=M0)
    state = TacticState(TypingContext(), Abstraction(X, Abstraction(Y, Hole(H))), typ)
    out = tactic_by_cases(state, H)
    assert out is not None
    assert out.term.body.body.cond == Var(Y)


def test_state_accounts_for_consumption_outside_focal_hole():
    f, arg = Name("f", 4), Name("arg", 5)
    ctx = TypingContext().with_var(X, t_int)
    full_ctx = TypingContext().with_var(
        f, AbstractionType(arg, t_int, AbstractionType(arg, t_int, t_int, multiplicity=M1), multiplicity=M1)
    )
    typ = AbstractionType(X, t_int, t_int, multiplicity=M1)

    def sketch(candidate):
        return Annotation(Abstraction(X, Application(Application(Var(f), Var(X)), candidate)), typ)

    validator = QTTValidator(lambda _: True, sketch, full_ctx)
    state = TacticState(ctx, Hole(H), t_int, validator.feasible)
    assert state.qtt_feasible()
    assert tactic_assumption(state, H) is None
    out = tactic_choose_literal(state, H)
    assert out is not None and out.check_sketch == state.check_sketch


@pytest.mark.parametrize(
    "tactic",
    [
        tactic_assumption,
        tactic_apply_question,
        tactic_constructor,
        tactic_by_cases,
        tactic_choose_literal,
        tactic_split,
        tactic_inst,
    ],
)
def test_every_tactic_respects_sketch_check(tactic):
    ctx = _prelude_ctx().with_var(X, t_int).with_var(Y, t_bool)
    typ = t_int
    if tactic is tactic_split:
        typ = RefinedType(
            Name("v", 9), t_int, LiquidApp(Name("&&", 0), [LiquidLiteralBool(True), LiquidLiteralBool(True)])
        )
    elif tactic is tactic_inst:
        typ = parse_type("forall a:B, a")
    state = TacticState(ctx, Annotation(Hole(H), typ), typ, lambda _: False)
    assert tactic(state, H) is None


def test_explicit_script_enforces_linear_goal_with_permissive_validator():
    typ = AbstractionType(X, t_int, t_int, multiplicity=M1)
    args = (TypingContext(), typ, lambda _: True, lambda _: [], Name("target", 10), {})
    ui = SilentSynthesisUI()
    assert ExplicitTacticSynthesizer(("constructor", "choose_literal")).synthesize(*args, ui=ui) is None
    assert ExplicitTacticSynthesizer(("constructor", "assumption")).synthesize(*args, ui=ui) is not None


def test_random_tactic_search_preserves_linear_goal():
    from aeon.synthesis.tactics.random_synth import TacticRandomSynthesizer

    typ = AbstractionType(X, t_int, t_int, multiplicity=M1)
    term = TacticRandomSynthesizer().synthesize(
        TypingContext(),
        typ,
        lambda _: True,
        lambda _: [],
        Name("target", 10),
        {},
        budget=2,
        ui=SilentSynthesisUI(),
    )
    assert TacticState(TypingContext(), term, typ).qtt_feasible()


@pytest.mark.parametrize(
    "source",
    [
        "def consume (1 x:Int):Int := by assumption; def main (u:Int):Int := consume 7;",
        "def erase (0 x:Int):Int := by choose_literal; def main (u:Int):Int := erase 7;",
    ],
)
def test_driver_supplies_surrounding_sketch_to_tactics(source):
    from tests.tdsyn_relations_test import _driver
    from aeon.typechecking.linearity import check_linearity

    driver = _driver(source)
    driver.synth()
    assert not check_linearity(driver.core, driver.typing_ctx)
    assert isinstance(driver.run(), int)
