"""Algorithm, soundness gate, replay, and section-4 data generation regressions."""

from __future__ import annotations

from dataclasses import replace
from math import log, sqrt
from pathlib import Path
import subprocess
import sys

import pytest
import z3
from hypothesis import given, settings, strategies as st

from aeon.core.terms import Application, Hole, If, Literal
from aeon.core.types import t_int, top
from aeon.lsp.server import SYNTHESIZERS
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.decorators import Goal
from aeon.synthesis.entrypoint import make_program, make_validator, synthesize_holes
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.rl_mcts import RLMCTSSynthesizer
from aeon.synthesis.modules.rl_mcts import search as engine
from aeon.synthesis.modules.rl_mcts import synthesizer as adapter
from aeon.synthesis.modules.rl_mcts.dataset import anti_unify, generate_problem, generate_problems, solve_generated
from aeon.synthesis.modules.rl_mcts.features import Syntax, policy_features, syntax, term_features, value_features
from aeon.synthesis.modules.rl_mcts.learning import LearnedGuidance, Replay, train, training_data
from aeon.synthesis.modules.rl_mcts.search import DefaultGuidance, Node, SearchConfig, search, uct
from aeon.synthesis.modules.rl_mcts.synthesizer import grammar_successors
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, TypedHole, locate_holes
from aeon.synthesis.modules.synthesizerfactory import is_known_synthesizer, make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import ReflectedBinder, TypingContext, UninterpretedBinder, VariableBinder
from aeon.utils.name import Name

from tests.driver import check_and_return_core


def tiny_search(*, goal="good", guidance=None, budget=5, config=SearchConfig(rollouts=10)):
    checked = []

    def verify(state):
        checked.append(state)
        return state == goal

    result = search(
        "root",
        Syntax("spec"),
        lambda s: Syntax(s),
        lambda s: int(s == "root"),
        lambda s: ["bad", "good"] if s == "root" else [],
        verify,
        config=config,
        budget=budget,
        guidance=guidance,
        seed=17,
    )
    return result, checked


def test_factory_and_lsp_registration(monkeypatch):
    monkeypatch.setenv("AEON_SEED", "17")
    assert is_known_synthesizer("rl_mcts")
    assert "rl_mcts" in SYNTHESIZERS
    backend = make_synthesizer("rl_mcts")
    assert isinstance(backend, RLMCTSSynthesizer) and backend.seed == 17


def test_uct_matches_paper_and_unvisited_zero_prior_is_explored():
    parent = Node("p", Syntax("p"), 1, visits=12)
    child = Node("c", Syntax("c"), 1, visits=3, total=1.2, prior=0.4)
    assert uct(parent, child, 2) == pytest.approx(1.2 / 3 + 2 * 0.4 * sqrt(log(12) / 3))
    assert uct(parent, Node("new", Syntax("new"), 1, prior=0)) == float("inf")


def test_default_guidance_matches_paper():
    guidance = DefaultGuidance()
    assert guidance.value(Syntax("s"), Syntax("h"), 3) == pytest.approx(0.95**3)
    assert guidance.policy(Syntax("s"), Syntax("h"), Syntax("c")) == 1


def test_big_steps_commit_by_visits_and_decay_value_backpropagation():
    class Guidance:
        def value(self, *_args):
            return 1.0

        def policy(self, *_args):
            return 1.0

    result = search(
        0,
        Syntax("spec"),
        lambda s: Syntax(str(s)),
        lambda s: int(s < 2),
        lambda s: [s + 1],
        lambda s: s == 2,
        guidance=Guidance(),
        config=SearchConfig(rollouts=1, big_steps=3, decay=0.98),
    )
    assert result.solution.state == 2
    assert [n.state for n in result.solution.path()] == [0, 1, 2]
    assert result.nodes[0].total == pytest.approx(1)
    assert result.nodes[1].total == pytest.approx(0.98)


def test_only_complete_states_are_verified_and_seeded_search_is_repeatable():
    first, checked = tiny_search()
    second, checked_again = tiny_search()
    assert first.solution.state == "good"
    assert checked == checked_again and "root" not in checked
    assert second.solution.state == first.solution.state
    assert first.root.visits > 0


def test_invalid_terminal_is_not_rechecked_and_exhaustion_stops():
    result, checked = tiny_search(goal="missing")
    assert result.solution is None and result.reason == "exhausted"
    assert sorted(checked) == ["bad", "good"]


def test_empty_grammar_stops_without_verification():
    result = search(
        0, Syntax("s"), lambda _: Syntax("h"), lambda _: 1, lambda _: [], lambda _: pytest.fail("not terminal")
    )
    assert result.reason == "exhausted"


def test_expired_budget_does_not_call_oracle():
    result, checked = tiny_search(budget=0)
    assert result.reason == "timeout" and checked == []


def test_clock_budget_and_node_limit(monkeypatch):
    ticks = iter([0, 0, 2])
    monkeypatch.setattr(engine, "monotonic", lambda: next(ticks))
    result, checked = tiny_search(budget=1)
    assert result.reason == "timeout" and checked == []
    monkeypatch.undo()
    result, _ = tiny_search(config=SearchConfig(max_nodes=2))
    assert result.reason == "node limit"


@pytest.mark.parametrize(
    "kwargs", [{"rollouts": 0}, {"big_steps": 0}, {"max_nodes": 0}, {"exploration": -1}, {"decay": 0}, {"decay": 2}]
)
def test_invalid_search_configuration(kwargs):
    with pytest.raises(ValueError):
        SearchConfig(**kwargs)


def test_successful_replay_uses_visit_ratio_and_discounted_distance():
    result, _ = tiny_search()
    replay = training_data(Syntax("spec"), result, bins=16)
    assert [label for _, label in replay.values] == pytest.approx([0.9, 1])
    parent, child = result.solution.path()
    assert replay.policies[0][1] == child.visits / sum(c.visits for c in parent.children)
    assert all(len(vector) == 32 for vector, _ in replay.values)
    assert all(len(vector) == 48 for vector, _ in replay.policies)


def test_failed_search_produces_zero_value_labels_and_no_policy_labels():
    result, _ = tiny_search(goal="missing")
    replay = training_data(Syntax("spec"), result, bins=16)
    assert replay.values and all(label == 0 for _, label in replay.values)
    assert replay.policies == []


def test_term_walk_counts_and_feature_shapes():
    tree = Syntax("+", (Syntax("x"), Syntax("1")))
    assert sum(term_features(tree, 4093)) == 5  # 3 symbols, 2 parent/child walks
    assert len(value_features(tree, tree, 17)) == 34
    assert len(policy_features(tree, tree, tree, 17)) == 51
    assert term_features(tree) == term_features(tree)
    with pytest.raises(ValueError):
        term_features(tree, 0)


def test_fresh_hole_ids_do_not_change_features():
    assert syntax(Hole(Name("h", 1))) == syntax(Hole(Name("h", 99)))


def test_aeon_expansion_restores_textual_leftmost_hole_order(monkeypatch):
    left, right = Name("left", 1), Name("right", 2)
    term = Application(Hole(left), Hole(right))
    paths = locate_holes(term)
    ctx = TypingContext()
    holes = [TypedHole(n, t_int, ctx, path=paths[n]) for n in (right, left)]
    partial = PartialAST(term, list(reversed(holes)), 0)
    monkeypatch.setattr(adapter, "expansions_for_hole", lambda *_args: [PartialAST(term, holes, 1)])
    (next_state,) = grammar_successors(partial, lambda _: False, 8, lambda p: syntax(p.term))
    assert [h.name for h in next_state.holes] == [left, right]


def test_actual_cli_example_runs_with_registered_backend():
    source = Path(__file__).resolve().parents[1] / "examples/synthesis/rl_mcts.ae"
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "-s", "rl_mcts", "--budget", "10", str(source)],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "Synthesized holes:" in result.stdout


def test_anti_unification_preserves_repeated_disagreement_pairs():
    a, b = z3.Ints("a b")
    generalized = anti_unify((a + a, b + b))
    assert len(generalized.params) == 1
    p = generalized.params[0]
    assert generalized.term.eq(p + p)
    assert generalized.arguments[0][0].eq(a)
    assert generalized.arguments[1][0].eq(b)


def test_common_source_variables_are_lifted_into_parameters():
    x = z3.Int("x")
    generalized = anti_unify((x + 1, x + 2))
    assert len(generalized.params) == 2
    assert all(any(v.eq(p) for p in generalized.params) for v in z3.z3util.get_vars(generalized.term))


def test_generated_problem_witness_restores_source_and_wrong_function_fails():
    x, y = z3.Ints("x y")
    source = z3.And(x + 1 == 1 + x, y + 2 == 2 + y)
    problem = generate_problem(source, (x + 1, y + 2))
    assert problem.verify(problem.witness)
    assert not problem.verify(z3.IntVal(0))
    text = problem.to_sygus()
    assert "(set-logic LIA)" in text and "(synth-fun" in text and "(constraint" in text
    with pytest.raises(ValueError, match="outside"):
        problem.verify(z3.Int("unbound"))


@settings(max_examples=20, deadline=None)
@given(st.integers(-100, 100), st.integers(-100, 100))
def test_generated_addition_witness_is_sound_for_arbitrary_constants(a, b):
    x, y = z3.Ints("x y")
    source = z3.And(x + a == a + x, y + b == b + y)
    problem = generate_problem(source, (x + a, y + b))
    assert problem.verify(problem.witness)
    assert a in problem.constants and b in problem.constants


def test_generated_sygus_is_accepted_and_solved_by_cvc5():
    import cvc5

    x, y = z3.Ints("x y")
    problem = generate_problem(z3.And(x + 1 == 1 + x, y + 2 == 2 + y), (x + 1, y + 2))
    solver = cvc5.Solver()
    solver.setOption("sygus", "true")
    solver.setOption("tlimit-per", "2000")
    symbols = cvc5.SymbolManager(solver)
    parser = cvc5.InputParser(solver, symbols)
    parser.setStringInput(cvc5.InputLanguage.SYGUS_2_1, problem.to_sygus(), "generated.sl")
    commands = []
    result = ""
    while True:
        command = parser.nextCommand()
        if command.isNull():
            break
        commands.append(command.getCommandName())
        result = command.invoke(solver, symbols)
    assert commands[-1] == "check-synth" and "define-fun" in result


def test_nonlinear_generalization_is_rejected_even_when_source_is_linear():
    x, y = z3.Ints("x y")
    source = z3.And(2 * x == x + x, 3 * y == y + y + y)
    with pytest.raises(ValueError, match="nonlinear"):
        generate_problem(source, (2 * x, 3 * y))


def test_invalid_or_satisfiable_only_training_sources_are_rejected():
    x = z3.Int("x")
    with pytest.raises(ValueError, match="valid"):
        generate_problem(x + 1 == x + 2, (x + 1, x + 2))
    with pytest.raises(ValueError, match="valid"):
        generate_problem(x + 1 == 2, (x + 1, z3.IntVal(2)))
    with pytest.raises(ValueError, match="quantifier"):
        generate_problems(z3.ForAll([x], x == x))
    with pytest.raises(ValueError, match="nonlinear"):
        generate_problems(x * x == x * x)


def test_unknown_source_validity_is_rejected(monkeypatch):
    x = z3.Int("x")
    monkeypatch.setattr(z3.Solver, "check", lambda _: z3.unknown)
    with pytest.raises(ValueError, match="valid"):
        generate_problem(x + 1 <= x + 2, (x + 1, x + 2))


def test_overlapping_and_mismatched_subterms_are_rejected():
    x = z3.Int("x")
    expr = (x + 1) + 2
    with pytest.raises(ValueError, match="non-overlapping"):
        generate_problem(expr == expr, (expr, x + 1))
    with pytest.raises(ValueError, match="same sort"):
        anti_unify((x, z3.BoolVal(True)))


def test_automatic_generation_and_search_do_not_need_witness():
    x = z3.Int("x")
    problems = generate_problems(x + 1 <= x + 2)
    assert problems and all(p.verify(p.witness) for p in problems)
    problems[0].witness = z3.IntVal(999)  # invalid witness must not influence search
    _, result = solve_generated(problems[0], config=SearchConfig(rollouts=100), budget=5)
    assert result.solution is not None


@pytest.mark.parametrize(
    "source",
    [
        "def n : {v:Int | v = 3} := ?h;",
        "def f (x:Int) : {v:Int | v = x} := ?h;",
        "def f (x:{v:Int | v > 0}) : {r:Int | r > 0} := ?h;",
        "def b : {v:Bool | v = true} := ?h;",
    ],
)
def test_real_aeon_refinement_holes(source):
    core, ctx, ectx, metadata = check_and_return_core(source)
    backend = RLMCTSSynthesizer(config=SearchConfig(rollouts=100))
    mapping = synthesize_holes(
        ctx, ectx, core, incomplete_functions_and_holes(ctx, core), metadata, backend, budget=10, ui=SilentSynthesisUI()
    )
    assert mapping and all(value is not None and not isinstance(value, Hole) for value in mapping.values())
    assert backend.last_result.solution is not None


def test_real_aeon_component_application_is_verified():
    source = "def step (x:Int) : {v:Int | v = x + 1} := x + 1; def successor (x:Int) : {v:Int | v = x + 1} := ?h;"
    core, ctx, ectx, metadata = check_and_return_core(source)
    backend = RLMCTSSynthesizer(config=SearchConfig(rollouts=300))
    mapping = synthesize_holes(
        ctx, ectx, core, incomplete_functions_and_holes(ctx, core), metadata, backend, budget=10, ui=SilentSynthesisUI()
    )
    assert mapping and backend.last_result.solution is not None


def test_real_aeon_conditional_is_synthesized_and_verified():
    source = "def bit (flag:Bool) : {v:Int | (flag && v = 1) || (!flag && v = 0)} := ?h;"
    core, ctx, _, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    fun_name, (hole,) = targets[0]
    target, hole_ctx = get_holes_info(ctx, core, top, targets, refined_types=True)[hole]
    # Restrict the component grammar to the parameter and structural actions.
    # The final whole-program verifier still has the normal prelude context.
    proposal_ctx = replace(
        hole_ctx,
        entries=[
            e
            for e in hole_ctx.entries
            if not isinstance(e, (VariableBinder, UninterpretedBinder, ReflectedBinder)) or e.name.name == "flag"
        ],
    )
    backend = RLMCTSSynthesizer(config=SearchConfig(rollouts=1000), max_depth=1)
    result = backend.synthesize(
        proposal_ctx,
        target,
        make_validator(ctx, make_program(core, hole)),
        lambda _: [],
        fun_name,
        metadata,
        budget=15,
        ui=SilentSynthesisUI(),
    )
    assert isinstance(result, If)
    assert backend.last_result.solution is not None


def test_direct_aeon_training_callback_and_learned_search(tmp_path):
    pytest.importorskip("xgboost", reason="optional synthesis-rl extra")
    from aeon.synthesis.modules.rl_mcts.training import aeon_problem

    source = tmp_path / "train.ae"
    source.write_text("def f (x:Int) : {v:Int | v = x} := ?h;", encoding="utf-8")
    problem = aeon_problem(source, budget=5, config=SearchConfig(rollouts=100))
    model, replays = train([problem], iterations=2, bins=16, estimators=3)
    assert len(replays) == 2 and all(r.policies for r in replays)
    _, held_out = problem(model)
    assert held_out.solution is not None


def test_optimization_goals_are_explicitly_unsupported():
    f = Name("f", 0)
    with pytest.raises(SynthesisNotSuccessful, match="optimization"):
        RLMCTSSynthesizer().synthesize(
            TypingContext(), t_int, lambda _: True, lambda _: [1.0], f, {f: {"goals": [Goal(True, 1, f)]}}
        )


def test_invalid_aeon_candidates_never_escape_acceptance_gate():
    backend = RLMCTSSynthesizer(config=SearchConfig(rollouts=100), max_depth=0)
    with pytest.raises(SynthesisNotSuccessful):
        backend.synthesize(
            TypingContext(), t_int, lambda _: False, lambda _: pytest.fail("no objectives"), Name("f", 0), {}, budget=5
        )
    assert backend.last_result.solution is None


def test_train_and_checkpoint_round_trip(tmp_path):
    pytest.importorskip("xgboost", reason="optional synthesis-rl extra")
    calls = []

    def problem(guidance):
        calls.append(guidance)
        result, _ = tiny_search(guidance=guidance)
        return Syntax("spec"), result

    model, replay = train([problem], iterations=2, bins=16, estimators=3)
    assert calls[0] is None and isinstance(calls[1], LearnedGuidance)
    assert len(replay) == 2 and all(r.values and r.policies for r in replay)
    model.save(tmp_path)
    restored = LearnedGuidance.load(tmp_path)
    assert restored.value(Syntax("spec"), Syntax("root"), 1) == pytest.approx(
        model.value(Syntax("spec"), Syntax("root"), 1)
    )
    assert restored.policy(Syntax("spec"), Syntax("root"), Syntax("good")) == pytest.approx(
        model.policy(Syntax("spec"), Syntax("root"), Syntax("good"))
    )


def test_training_requires_a_success_and_matching_feature_width():
    pytest.importorskip("xgboost", reason="optional synthesis-rl extra")
    with pytest.raises(ValueError, match="successful"):
        LearnedGuidance.fit(Replay([([0.0] * 32, 0)], []), bins=16)
    with pytest.raises(ValueError, match="width"):
        LearnedGuidance.fit(Replay([([0.0], 0)], [([0.0], 1)]), bins=16)


def test_learned_backend_still_requires_validator_acceptance(monkeypatch, tmp_path):
    pytest.importorskip("xgboost", reason="optional synthesis-rl extra")
    model, _ = train([lambda g: (Syntax("spec"), tiny_search(guidance=g)[0])], iterations=1, bins=16, estimators=2)
    model.save(tmp_path)
    monkeypatch.setenv("AEON_RL_MCTS_MODEL", str(tmp_path))
    backend = RLMCTSSynthesizer(max_depth=0)
    seen = []

    def validate(term):
        seen.append(term)
        return isinstance(term, Literal) and term.value == 7

    result = backend.synthesize(
        TypingContext(), t_int, validate, lambda _: pytest.fail("no objectives"), Name("f", 0), {}, budget=5
    )
    assert result == Literal(7, t_int) and seen
