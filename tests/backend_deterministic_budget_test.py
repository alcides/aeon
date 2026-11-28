"""Each enabled backend must solve a real problem without a time allowance."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.budgets import DeterministicBudget
from aeon.synthesis.uis.api import SilentSynthesisUI


IDENTITY = """
@example(f 0 = 0)
@example(f 1 = 1)
def f(x:Int):{r:Int | r = x} := ?hole;
"""


def solve(backend, source, opcodes=2_000_000, evaluation_opcodes=1_000_000):
    driver = AeonDriver(
        AeonConfig(
            backend,
            SilentSynthesisUI(),
            0,
            no_main=True,
            deterministic_budget=DeterministicBudget(opcodes, evaluation_opcodes, smt_rlimit=1_000_000),
        )
    )
    assert not list(driver.parse(aeon_code=source))
    assert driver.has_synth()
    driver.synth()
    return driver


@pytest.mark.parametrize(
    "backend",
    [
        "sygus",
        "polynomial",
        "synquid",
        "fta",
        "afta",
        "cata",
        "contata",
        "lta",
        "symetric",
        "arborist",
        "amaze",
        "bustle",
        "bustle_baseline",
        "rl_mcts",
        "decision_tree",
        "tactics",
        "noisy",
    ],
)
def test_backend_solves_with_zero_seconds(backend):
    source = IDENTITY
    if backend == "polynomial":
        source = "def f(x:Int):{r:Int | r = x} := ?hole;"
    elif backend == "symetric":
        source = "@minimize_int(n) def n:{v:Int | v >= 0 && v <= 1} := ?hole;"
    elif backend == "decision_tree":
        source = IDENTITY.replace("x:Int", "x:{v:Int | v >= 0 && v <= 1}")
    elif backend == "tactics":
        source = "def n:Int := ?hole;"
    # Grammar preparation grows with the standard library; quotas remain work-based.
    solve(backend, source, opcodes=100_000_000 if backend == "noisy" else 10_000_000)


def test_boolean_cegis_uses_resource_limits():
    solve("boolean_bounded", "@bounded_cnf(1) def f(x:Bool):{r:Bool | r = x} := ?hole;")


def test_cp_sat_uses_deterministic_work_and_one_worker():
    pytest.importorskip("ortools")
    solve("ortools", "@minimize_int(n) def n:{v:Int | v >= 0 && v <= 10 && v = 3} := ?hole;")


def test_structure_guided_uses_bounded_search():
    from tests.structure_guided_synthesis_test import LIST

    solve(
        "structure_guided",
        LIST
        + """
    @example(f Chain.nil = Chain.nil)
    @example(f (Chain.cons 1 Chain.nil) = Chain.cons 1 Chain.nil)
    @allow_recursion
    def f(xs:Chain):Chain := ?hole;
    """,
    )


def test_regus_uses_bounded_search_and_observations(monkeypatch):
    from tests.regus_test import TOY
    from aeon.synthesis.modules.regus import ReGuSSynthesizer
    from aeon.synthesis.modules.regus.search import Config

    backend = ReGuSSynthesizer(
        config=Config(
            max_nodes=3,
            max_loops=1,
            max_sketch_nodes=3,
            max_states=64,
            completion_batch=1,
        )
    )
    monkeypatch.setattr("aeon.facade.driver.make_synthesizer", lambda _name, **_options: backend)
    solve("regus", TOY.replace("DESIRED", "0"), opcodes=50_000_000, evaluation_opcodes=10_000_000)


def test_one_step_literal_tactic_uses_quota():
    solve("backward_lit", "def n:Int := ?hole;")


@pytest.mark.parametrize("backend", ["enumerative", "boolean_bounded"])
def test_property_corpora_and_evaluation_use_quotas(backend):
    if backend == "boolean_bounded":
        source = "@bounded_cnf(1) def f(x:Bool):Bool := ?hole; @property(2) def law(x:Bool):Bool := f x = x;"
    else:
        source = "def f(x:Int):Int := ?hole; @property(4) def law(x:Int):Bool := f x = x;"
    solve(backend, source)


def test_explicit_tactic_script_uses_quota():
    # Exact script syntax is covered by the tactic tests; check the adapter here.
    from aeon.core.types import t_int
    from aeon.typechecking.context import TypingContext
    from aeon.synthesis.budgets import budget_scope, run_budgeted_search
    from aeon.synthesis.tactics.explicit_synth import ExplicitTacticSynthesizer
    from aeon.utils.name import Name

    backend = ExplicitTacticSynthesizer(("choose_literal",))
    backend.deterministic_budget = DeterministicBudget(100_000)
    with budget_scope(backend.deterministic_budget):
        result = run_budgeted_search(
            backend,
            backend.synthesize,
            ctx=TypingContext(),
            type=t_int,
            validate=lambda _term: True,
            evaluate=lambda _term: [],
            fun_name=Name("f", 0),
            metadata={},
            budget=0,
            ui=SilentSynthesisUI(),
        )
    assert result is not None


def test_low_level_synthesis_scopes_solver_limits_without_replacing_compiler_state():
    from aeon.synthesis.entrypoint import synthesize_holes
    from aeon.synthesis.modules.enumerative import EnumerativeSynthesizer
    from aeon.verification.state import VerificationState

    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
    assert not list(driver.parse(aeon_code="def n:{v:Int | v = 7} := ?hole;"))
    assert driver.has_synth()
    backend = EnumerativeSynthesizer()
    backend.deterministic_budget = DeterministicBudget(1_000_000)
    with driver.session.activate():
        state = driver.session.state(VerificationState)
        options = driver.session.options
        result = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            driver.incomplete_functions,
            driver.metadata,
            backend,
            budget=0,
            ui=SilentSynthesisUI(),
        )
        assert all(value is not None for value in result.values())
        assert driver.session.options is options
        assert driver.session.state(VerificationState) is state


def test_swallowed_worker_watchdog_still_aborts_the_whole_run():
    from aeon.synthesis.budgets import budget_scope, raise_watchdog, EvaluationWatchdogExpired

    with pytest.raises(EvaluationWatchdogExpired, match="safety watchdog"):
        with budget_scope(DeterministicBudget(1000)):
            try:
                raise_watchdog("safety watchdog")
            except Exception:
                pass  # Simulate a backend's broad candidate-error handler.


def test_child_watchdog_is_propagated_as_a_fatal_run_failure():
    from aeon.synthesis.budgets import budget_scope, raise_watchdog, EvaluationWatchdogExpired
    from aeon.synthesis.evaluation_pool import EvaluationPool
    from aeon.core.terms import Literal
    from aeon.core.types import t_int

    def failed_native_call(_program):
        raise_watchdog("child watchdog")

    with pytest.raises(EvaluationWatchdogExpired, match="child watchdog"):
        with budget_scope(DeterministicBudget(1000)):
            pool = EvaluationPool(lambda term: term, {"fitness": failed_native_call})
            try:
                pool.run(Literal(0, t_int))
            finally:
                pool.close()


def test_learned_guidance_is_bounded_and_forced_to_one_cpu_thread(tmp_path):
    import math

    pytest.importorskip("xgboost")
    from aeon.synthesis.budgets import budget_scope, evaluate_deterministically
    from aeon.synthesis.modules.rl_mcts.learning import LearnedGuidance, Replay

    replay = Replay(
        values=[([0.0] * 4, 0.0), ([1.0] * 4, 1.0)],
        policies=[([0.0] * 6, 0.0), ([1.0] * 6, 1.0)],
    )
    model = LearnedGuidance.fit(replay, bins=2, estimators=2)
    model.save(tmp_path)
    with budget_scope(DeterministicBudget(100_000)):
        restored = LearnedGuidance.load(tmp_path)
        prediction = evaluate_deterministically(restored._predict, restored.value_model, [0.0] * 4)
    assert math.isfinite(prediction)
    assert restored.value_model.get_params()["n_jobs"] == 1
    assert restored.value_model.get_params()["device"] == "cpu"


def test_neural_boolean_backend_rejects_unmetered_training():
    from aeon.synthesis.api import SynthesisNotSuccessful

    with pytest.raises(SynthesisNotSuccessful, match="PyTorch training"):
        solve("bnsynth", "@bounded_cnf(1) def f(x:Bool):{r:Bool | r = x} := ?hole;")
