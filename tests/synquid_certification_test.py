"""Construction discharges proofs without a second candidate type checker."""

from itertools import islice

import pytest

from aeon.core.liquid import LiquidLiteralInt, LiquidVar
from aeon.core.terms import Application, Var
from aeon.core.types import t_int, top
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.synquid.constraints import ConstraintState
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.synthesis.modules.synquid.solver import SMTQuery, Status
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.verification.vcs import LiquidConstraint
from tests.driver import check_and_return_core
from tests.synquid_round_trip_test import liq, name, parse_type


def test_mus_semantic_minimization_avoids_pairwise_qualifier_preprocessing():
    x = LiquidVar(name("x"))
    ctx = TypingContext().with_var(name("x"), t_int)
    state = ConstraintState(ctx)
    count = 32
    qualifiers = frozenset(liq(">=", x, LiquidLiteralInt(i)) for i in range(count))
    predicate = state.fresh_predicate(ctx, qualifiers)
    goal = liq(">=", x, LiquidLiteralInt(0))
    state.add(state.assume(predicate).lift(LiquidConstraint(goal)), lifted=True)
    assert state.solve() == Status.VALID
    assert len(state.assignments) == 1
    # All singleton MUSes suffice; semantic minimization retains x >= 0.
    from aeon.verification.horn import apply_liquid

    actual = apply_liquid(state.assignments[0], predicate)
    assert state.assume(goal).query.valid(state.assume(goal).lift(LiquidConstraint(actual))) == Status.VALID
    assert state.stats.unsat_cores > 0
    # Eager qualifier ordering alone required count*(count-1) comparisons.
    assert state.stats.solver_queries < count * (count - 1)


@pytest.mark.parametrize("goal", ["{v:Int | v == 1}", "{v:Bool | !v}", "(x:Int) -> {v:Int | v == x}"])
def test_every_emitted_term_has_its_goal_type(goal):
    goal = parse_type(goal)
    ctx = built_std_context()
    terms = list(islice(synthes_memory(ctx, 1, goal, lambda n: n.name != "x", {}), 20))
    assert terms
    assert all(check_type(ctx, term, goal) for term in terms)


@pytest.mark.parametrize("status", [Status.UNKNOWN, Status.UNSUPPORTED])
def test_incomplete_proofs_never_emit_completed_candidates(monkeypatch, status):
    monkeypatch.setattr(SMTQuery, "valid", lambda *args: status)
    ctx = built_std_context()
    goal = parse_type("{v:Int | v == 1}")
    assert list(synthes_memory(ctx, 0, goal, lambda _: True, {}, conditionals=False)) == []


def test_entrypoint_does_not_retypecheck_synquid_candidates(monkeypatch):
    program, root, runtime, metadata = check_and_return_core("def answer:{v:Int | v = 7} := ?h;")
    targets = incomplete_functions_and_holes(root, program)
    owner, (hole,) = targets[0]
    metadata.setdefault(owner, {})["synquid_max_level"] = 0

    def forbidden(*args):
        pytest.fail("Synquid must use construction proofs, not whole-program candidate typechecking")

    monkeypatch.setattr("aeon.synthesis.entrypoint.check_type", forbidden)
    backend = SynquidSynthesizer()
    result = synthesize_holes(root, runtime, program, targets, metadata, backend, budget=5, ui=SilentSynthesisUI())
    goal, ctx = get_holes_info(root, program, top, targets, refined_types=True)[hole]
    assert check_type(ctx, result[hole], goal)
    assert backend.stats.full_validations == 0
    assert backend.stats.specification_checks > 0


def test_non_type_cnf_contract_is_still_enforced():
    program, root, runtime, metadata = check_and_return_core("@bounded_cnf(0) def answer:{v:Bool | !v} := ?h;")
    targets = incomplete_functions_and_holes(root, program)
    owner, _ = targets[0]
    metadata.setdefault(owner, {})["synquid_max_level"] = 0
    with pytest.raises(SynthesisNotSuccessful):
        synthesize_holes(
            root, runtime, program, targets, metadata, SynquidSynthesizer(), budget=5, ui=SilentSynthesisUI()
        )


@pytest.mark.parametrize("extra_parameter", ["", "(step:(x:Int) -> Int)"])
def test_source_recursive_calls_are_constrained_before_generation(extra_parameter):
    program, root, _, metadata = check_and_return_core(
        f"@allow_recursion def loop(n:Int | n >= 0) {extra_parameter}:Int decreasing_by [n] := ?h;"
    )
    targets = incomplete_functions_and_holes(root, program)
    owner, (hole,) = targets[0]
    _, ctx = get_holes_info(root, program, top, targets, refined_types=True)[hole]
    n = next(n for n, _ in ctx.vars() if n.name == "n")
    ctx = SynquidSynthesizer().prepare_context(ctx, program, owner, metadata)

    def call(argument):
        term = Application(Var(owner), Var(argument))
        if extra_parameter:
            step = next(n for n, _ in ctx.vars() if n.name == "step")
            term = Application(term, Var(step))
        return term

    assert not check_type(ctx, call(n), t_int)
    from aeon.core.types import RefinedType

    m, v = name("smaller"), name("v")
    smaller = RefinedType(
        v, t_int, liq("&&", liq(">=", LiquidVar(v), LiquidLiteralInt(0)), liq("<", LiquidVar(v), LiquidVar(n)))
    )
    assert check_type(ctx.with_var(m, smaller), call(m), t_int)
