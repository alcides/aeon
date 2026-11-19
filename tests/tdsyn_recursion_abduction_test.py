"""Recursive hypotheses from ``decreasing_by`` and branch-first guards on TDSyn."""

from time import monotonic
from types import SimpleNamespace

from aeon.core.liquid import LiquidApp, LiquidTerm, LiquidVar
from aeon.core.terms import Hole, If, Var
from aeon.core.types import t_int, top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.modules.synquid.abduction import AbductionResult
from aeon.synthesis.modules.synquid.solver import Status
from aeon.synthesis.modules.tdsyn.actions import abduced_if_candidates, backward_candidates, backward_if_candidates
from aeon.synthesis.modules.tdsyn import actions
from aeon.synthesis.modules.tdsyn.constraints import deadline
from aeon.synthesis.modules.tdsyn.helpers import make_skip_fn
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, expand_at_hole, fresh_hole
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name
from tests.synquid_round_trip_test import liq, name, parse_type


def _maximum():
    ctx = built_std_context().with_var(name("x"), t_int).with_var(name("y"), t_int)
    goal = parse_type("{v:Int | ((v >= x) && (v >= y)) && ((v == x) || (v == y))}")
    return ctx, goal


def _subterms(term: LiquidTerm) -> set[LiquidTerm]:
    found = {term}
    if isinstance(term, LiquidApp):
        for arg in term.args:
            found |= _subterms(arg)
    return found


def _hole(ctx, goal):
    _, hole = fresh_hole(goal, ctx)
    return hole


def test_decreasing_metric_weakens_the_hypothesis_and_opens_the_skip():
    driver = AeonDriver(AeonConfig("tdsyn_enumerative", SilentSynthesisUI(), 1))
    assert not list(driver.parse(filename="examples/benchmarks/synquid/List-Append.ae"))
    assert driver.has_synth()
    fun = driver.incomplete_functions[0][0]
    with driver.session.activate():
        info = get_holes_info(driver.typing_ctx, driver.core, top, driver.incomplete_functions, refined_types=True)
        ctx = next(context for hole, (_ty, context) in info.items() if hole.name == "hole")
        metadata = {fun: {}}
        weakened = TDSynSynthesizer().prepare_context(ctx, driver.core, fun, metadata)
        assert metadata[fun]["recursion"] is True
        assert make_skip_fn(fun, metadata)(fun) is False
        full = str(ctx.type_of(fun))
        hypothesis = str(weakened.type_of(fun))
        assert "<" not in full
        assert "<" in hypothesis


def test_no_metric_does_not_open_recursion():
    driver = AeonDriver(AeonConfig("tdsyn_enumerative", SilentSynthesisUI(), 1))
    assert not list(driver.parse(filename="examples/benchmarks/synquid/List-Null.ae"))
    assert driver.has_synth()
    fun = driver.incomplete_functions[0][0]
    with driver.session.activate():
        info = get_holes_info(driver.typing_ctx, driver.core, top, driver.incomplete_functions, refined_types=True)
        ctx = next(context for hole, (_ty, context) in info.items() if hole.name == "hole")
        metadata = {fun: {}}
        assert TDSynSynthesizer().prepare_context(ctx, driver.core, fun, metadata) == ctx
        assert "recursion" not in metadata[fun]
        assert make_skip_fn(fun, metadata)(fun) is True


def test_refined_guard_comes_from_abduce_and_is_not_a_goal_subterm():
    # ``x >= y`` decides which argument is the maximum. It does not occur in
    # the goal, whose atoms only relate the result to one argument at a time.
    ctx, goal = _maximum()
    hole = _hole(ctx, goal)
    candidates = abduced_if_candidates(hole, lambda _name: False)
    assert len(candidates) == 1
    term, children = candidates[0]
    assert isinstance(term, If)
    assert not isinstance(term.cond, Hole)
    assert not isinstance(term.then, Hole)
    assert isinstance(term.otherwise, Hole)
    assert len(children) == 1 and children[0].name == term.otherwise.name
    guard = liq(">=", LiquidVar(name("x")), LiquidVar(name("y")))
    assert guard not in _subterms(goal.refinement)
    from aeon.core.substitutions import liquefy

    assert liquefy(term.cond) == guard
    partial = expand_at_hole(PartialAST(Var(Name("root", 1)), [hole], 0), hole, term, children, 1)
    assert len(partial.holes) == 1
    assert any(isinstance(g, LiquidApp) and g.fun == Name("!", 0) for g in partial.holes[0].guards)
    assert check_type(ctx, If(term.cond, Var(name("x")), Var(name("y"))), goal)


def test_abduced_guard_is_the_value_abduce_returns(monkeypatch):
    ctx, goal = _maximum()
    flag = name("flag")
    ctx = ctx.with_var(flag, parse_type("Bool"))
    sentinel = Var(flag)

    def fake_abduce(state, branch, goal, **_kwargs):
        return AbductionResult([(LiquidVar(flag), sentinel)], Status.VALID, [LiquidVar(flag)])

    monkeypatch.setattr("aeon.synthesis.modules.synquid.abduction.abduce", fake_abduce)
    term, children = abduced_if_candidates(_hole(ctx, goal), lambda _name: False)[0]
    assert isinstance(term, If)
    assert term.cond == sentinel
    assert LiquidVar(flag) not in _subterms(goal.refinement)
    assert len(children) == 1


def test_unrefined_goal_keeps_the_three_hole_if(monkeypatch):
    def forbidden(*_args, **_kwargs):
        raise AssertionError("unrefined enumeration must not call abduce")

    monkeypatch.setattr("aeon.synthesis.modules.synquid.abduction.abduce", forbidden)
    ctx = built_std_context()
    _, hole = fresh_hole(t_int, ctx)
    term, children = backward_if_candidates(hole, lambda _name: False)[0]
    assert [isinstance(part, Hole) for part in (term.cond, term.then, term.otherwise)] == [True, True, True]
    assert len(children) == 3
    combined = backward_candidates(hole, lambda _name: False)
    assert any(isinstance(candidate, If) and isinstance(candidate.cond, Hole) for candidate, _holes in combined)


def test_abduction_shares_the_outer_deadline_and_limits_its_own_work(monkeypatch):
    ctx, goal = _maximum()
    seen = []
    monkeypatch.setattr(actions, "_then_arms", lambda *_: iter([Var(name("x"))]))
    monkeypatch.setattr(
        "aeon.synthesis.modules.synquid.abduction.branch_environment",
        lambda *_: SimpleNamespace(inhabited=lambda: Status.UNKNOWN),
    )

    def infer(state, *args):
        seen.append((state.deadline, state.query.deadline))
        return AbductionResult([], Status.UNKNOWN)

    monkeypatch.setattr("aeon.synthesis.modules.synquid.abduction.abduce", infer)
    for remaining in (0.1, 60):
        outer = monotonic() + remaining
        token = deadline.set(outer)
        try:
            assert abduced_if_candidates(_hole(ctx, goal), lambda _: False) == []
        finally:
            deadline.reset(token)
        bound, query_bound = seen[-1]
        assert query_bound == bound <= outer
        if remaining == 60:
            assert bound < outer


def test_expired_abduction_does_not_enumerate_arms(monkeypatch):
    def forbidden(*args):
        raise AssertionError("expired abduction must stop before constructing an arm")

    ctx, goal = _maximum()
    monkeypatch.setattr(actions, "_then_arms", forbidden)
    token = deadline.set(0)
    try:
        assert abduced_if_candidates(_hole(ctx, goal), lambda _: False) == []
    finally:
        deadline.reset(token)


def test_lazy_literals_do_not_eagerly_abduce_a_guard(monkeypatch):
    called = []
    monkeypatch.setattr(actions, "abduced_if_candidates", lambda *_: called.append(True) or [])
    hole = _hole(built_std_context(), parse_type("{v:Int | v >= 0}"))
    stream = actions.iter_backward_candidates(hole, lambda _: True)
    next(stream)
    stream.close()
    assert called == []


def test_failed_abduction_retains_refined_conditional_productions(monkeypatch):
    monkeypatch.setattr(actions, "abduced_if_candidates", lambda *_: [])
    for expand in (backward_candidates, actions.iter_backward_candidates):
        hole = _hole(built_std_context(), parse_type("{v:Int | v > 10}"))
        assert any(
            isinstance(term, If) and isinstance(term.cond, Hole) and len(children) == 3
            for term, children in expand(hole, lambda _: True)
        )


def _solve(filename: str, budget: int = 30):
    driver = AeonDriver(AeonConfig("tdsyn_enumerative", SilentSynthesisUI(), budget))
    assert not list(driver.parse(filename=filename))
    assert driver.has_synth()
    try:
        driver.synth()
    except SynthesisNotSuccessful:
        return False
    return True


def test_list_null_solves_under_tdsyn_enumerative():
    assert _solve("examples/benchmarks/synquid/List-Null.ae")


def test_list_append_solves_from_decreasing_by_under_tdsyn_enumerative():
    assert _solve("examples/benchmarks/synquid/List-Append.ae")
