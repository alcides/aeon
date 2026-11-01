"""AMaze's learning boundary, actual grammar/rank algorithm and CLI integration."""

from __future__ import annotations

from dataclasses import FrozenInstanceError, replace
from itertools import product
import json
import os
from pathlib import Path
import subprocess
import sys
from time import monotonic

import pytest

from aeon.compilation.resolve import resolve_module_source
from aeon.compilation.session import CompilationOptions, CompilationSession
from aeon.core.multiplicity import M1
from aeon.core.terms import Abstraction, Var
from aeon.core.types import AbstractionType, t_int
from aeon.synthesis.api import UnsupportedSynthesisGoal, SynthesisNotSuccessful
from aeon.synthesis.modules.amaze.core import from_core, to_core, unwrap, equivalent
from aeon.synthesis.modules.amaze.corpus import collect, checked_path, CorpusError
from aeon.synthesis.modules.amaze.grammar import (
    Expr,
    Production,
    Grammar,
    base_productions,
    instantiate,
    match,
    evaluate,
)
from aeon.synthesis.modules.amaze.learning import Config, fit, reconstruct
from aeon.synthesis.modules.amaze.mining import patterns, mine
from aeon.synthesis.modules.amaze.profile import DEFAULT_PROFILE, load
from aeon.synthesis.modules.amaze.synthesizer import AmazeSynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer, synthesizer_label
from aeon.utils.name import Name
from aeon.synthesis.uis.api import SilentSynthesisUI
from tests.joint_hole_synthesis_test import parse, solve, fill


@pytest.fixture(scope="module")
def corpus():
    return collect()


def test_package_only_resolution_and_transitive_imports(monkeypatch, tmp_path):
    for folder in (tmp_path, tmp_path / "libraries", tmp_path / "overrides"):
        folder.mkdir(exist_ok=True)
        (folder / "Refinement.ae").write_text('def poison : Int := native "raise Exception()";')
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("AEONPATH", str(tmp_path / "overrides"))
    assert resolve_module_source("Refinement") == str(tmp_path / "Refinement.ae")
    with CompilationSession(CompilationOptions(package_only_imports=True)).activate():
        assert "/aeon/libraries/Refinement.ae" in resolve_module_source("Refinement")
        from aeon.compilation.compile import compile_file, dependency_units_for

        math_path = resolve_module_source("Math")
        unit, errors = compile_file(math_path, use_cache=False, write_cache=False)
        assert not errors
        assert all("/aeon/libraries/" in u.source_path for u in dependency_units_for(unit))
    assert resolve_module_source("Refinement") == str(tmp_path / "Refinement.ae")


def test_symlink_escape_is_rejected(tmp_path, monkeypatch):
    base = tmp_path / "libraries"
    base.mkdir()
    outside = tmp_path / "outside.ae"
    outside.write_text("def x : Int := 0;")
    (base / "Escape.ae").symlink_to(outside)
    with pytest.raises(CorpusError, match="escapes"):
        checked_path(base / "Escape.ae", base.resolve())
    monkeypatch.setattr("aeon.compilation.resolve.get_package_libraries_dir", lambda: base)
    with CompilationSession(CompilationOptions(package_only_imports=True)).activate():
        with pytest.raises(ValueError, match="escapes"):
            resolve_module_source("Escape")


def test_corpus_has_only_real_stdlib_references_and_split_before_mining(corpus):
    tasks, report = corpus
    assert len(tasks) == 9
    assert report["eligible"] == 9 and report["skipped"] > 100
    assert all(Path(v["canonical_path"]).is_relative_to(report["root"]) for v in report["files"].values())
    assert all(report["files"][t.source]["sha256"] == t.source_hash for t in tasks)
    groups = {}
    for task in tasks:
        assert groups.setdefault(task.group, task.split) == task.split
        assert all(evaluate(task.reference, args) == out for args, out in task.examples)
        assert all(p.template.op in ("var", "const") or p.id.startswith("op:") for p in base_productions(task.inputs))
    assert any("native/effectful" in r.get("reason", "") for r in report["definitions"])
    training = [t for t in tasks if t.split == "train"]
    macros = mine(training)
    assert macros
    assert all(set(m["origins"]) <= {t.id for t in training} for m in macros)
    with pytest.raises(ValueError, match="training split"):
        mine(tasks)


def test_reconstruction_weak_types_do_not_accept_constant_zero(corpus):
    tasks, _ = corpus
    absolute = next(t for t in tasks if t.id == "Vec.ae:absolute")
    record, solution = reconstruct(absolute, (), Config(max_cost=1, max_candidates=100), monotonic() + 2)
    assert solution is None and record["censored"]
    assert record["candidates"] == 3  # two literals and the single argument, no self alias
    positive = next(t for t in tasks if t.id == "Refinement.ae:positive")
    record, solution = reconstruct(positive, (), Config(), monotonic() + 3)
    assert record["status"] == "solved"
    assert equivalent(solution, positive.reference, positive.inputs) == "equivalent"


def test_empty_corpus_is_not_a_trained_profile(monkeypatch):
    monkeypatch.setattr(
        "aeon.synthesis.modules.amaze.corpus.source_inventory", lambda: {"root": "/unused", "files": {}}
    )
    with pytest.raises(CorpusError, match="six independent"):
        collect()


def tiny():
    x = Expr("var", "Int", value=0)
    p = Expr("param", "Int", value=0)
    return (
        x,
        p,
        (
            Production("x", (), "Int", x),
            Production("zero", (), "Int", Expr("const", "Int", value=0)),
            Production("add", ("Int", "Int"), "Int", Expr("+", "Int", (p, replace(p, value=1)))),
        ),
    )


def exhaustive(grammar, sort, cost):
    # Independent tiny oracle: filter all child costs rather than DP compositions.
    terms = []
    for p in grammar.productions:
        if p.result != sort:
            continue
        for costs in product(range(1, cost + 1), repeat=len(p.arguments)):
            if sum(costs) + p.cost != cost:
                continue
            for children in product(*(exhaustive(grammar, s, n) for s, n in zip(p.arguments, costs))):
                terms.append(instantiate(p.template, children))
    return terms


def test_dp_matches_ordered_exhaustive_derivations_and_tied_parameters():
    x, p, base = tiny()
    double = Production("double", ("Int",), "Int", Expr("+", "Int", (p, p)))
    grammar = Grammar(base + (double,))
    for cost in range(1, 7):
        oracle = exhaustive(grammar, "Int", cost)
        assert grammar.count("Int", cost) == len(oracle)
        assert [grammar.unrank("Int", cost, i)[0] for i in range(len(oracle))] == oracle
    assert grammar.count("Int", 2) == 2  # tied argument enumerated once, not squared
    expression = Expr("+", "Int", (x, x))
    assert match(double.template, expression, 1) == (x,)
    assert match(double.template, Expr("+", "Int", (x, Expr("const", "Int", value=0))), 1) is None
    assert grammar.rewrite_cost(expression) == 2
    assert Grammar(base).rewrite_cost(expression) == 3
    assert grammar.estimate(expression) >= 3
    # Distinct derivations can expand to the same AST; no false distinct-AST claim.
    emitted = [e for e, _, _ in grammar.enumerate("Int", 5, 1000, monotonic() + 2)]
    assert len(emitted) > len(set(emitted))


def test_cycles_empty_grammars_large_counts_and_instance_local_caches():
    x, p, base = tiny()
    identity = Production("identity", ("Int",), "Int", p)
    assert Grammar((identity,)).count("Int", 8) == 0
    assert Grammar(()).count("Int", 2) == 0
    with pytest.raises(ValueError, match="positive"):
        replace(identity, cost=0)
    assert Grammar(base).count("Int", 101) > 2**64
    before = Grammar(base)
    assert before.count("Int", 2) == 0
    assert Grammar(base + (identity,)).count("Int", 2) == 2
    assert before.count("Int", 2) == 0


def test_pattern_alpha_renaming_capture_avoidance_and_core_type_checks():
    a, b = Name("a", 3), Name("a", 8)
    expr = Expr("+", "Int", (Expr("var", "Int", value=0), Expr("var", "Int", value=0)))
    assert from_core(to_core(expr, (a,)), {a: Expr("var", "Int", value=0)}) == expr
    assert from_core(to_core(expr, (b,)), {b: Expr("var", "Int", value=0)}) == expr
    template = next(t for t, args in patterns(expr) if args == ("Int",))
    assert template.children[0] == template.children[1]
    with pytest.raises(ValueError, match="unsupported Core"):
        from_core(Var(b), {a: Expr("var", "Int", value=0)})
    with pytest.raises(ValueError):
        Production("bad", (), "Int", Expr("native", "Int"))
    with pytest.raises(ValueError, match="multiplicities"):
        unwrap(Abstraction(a, Var(a)), AbstractionType(a, t_int, t_int, multiplicity=M1))


def test_real_model_consumes_successes_and_censored_lower_bounds():
    labels = [
        {"status": "solved", "censored": False, "rank_bound": 10, "candidates": 5, "elapsed": 0.01},
        {"status": "timeout", "censored": True, "reference_rank_bound": 1000, "candidates": 80, "elapsed": 1},
    ]
    m = fit(labels)
    assert m.slope > 0 and m.predict(10) < m.predict(1000)
    altered = fit([labels[0], labels[1] | {"candidates": 800}])
    assert altered != m
    with pytest.raises(CorpusError):
        fit([labels[1]])


def test_profile_is_versioned_and_has_real_search_refresh_and_held_out_report():
    p = load()
    report = json.loads(p.document)
    assert p.macros and report["search"]
    assert report["labels"] and all(r["split"] == "train" for r in report["labels"])
    assert any(r["phase"].startswith("refresh_") for r in report["labels"])
    assert any(s.get("selected") for s in report["search"])
    assert set(report["known_solutions"]) == {t["id"] for t in report["corpus"]["tasks"] if t["split"] == "train"}
    assert all(r["split"] == "held_out" for k in ("baseline", "optimized") for r in report["held_out"][k])
    assert report["cost_model"]["slope"] > 0
    with pytest.raises(FrozenInstanceError):
        p.document = "changed"


@pytest.mark.parametrize("mutation", ["schema", "hash", "origin", "primitive"])
def test_profile_rejects_incompatible_stale_and_nontraining_lineage(tmp_path, mutation):
    payload = json.loads(DEFAULT_PROFILE.read_text())
    if mutation == "schema":
        payload["schema"] = 999
    elif mutation == "hash":
        next(iter(payload["corpus"]["files"].values()))["sha256"] = "0" * 64
    elif mutation == "origin":
        payload["macros"][0]["origins"] = ["user_program.ae:secret"]
    else:
        payload["macros"][0]["template"] = ["native", "Bool", None, []]
    path = tmp_path / "bad.json"
    path.write_text(json.dumps(payload))
    with pytest.raises(ValueError):
        load(path)


def test_inference_is_immutable_and_uses_selected_grammar(tmp_path):
    path = tmp_path / "profile.json"
    path.write_bytes(DEFAULT_PROFILE.read_bytes())
    before = path.read_bytes()
    for distinctive in (1799, 2939):
        driver = parse(
            f"def distinct_helper (x:Int) : Int := x + {distinctive}; def f (x:Int) : {{v:Int | v = x + 1}} := ?h;"
        )
        backend = AmazeSynthesizer(path)
        with driver.session.activate():
            mapping = solve(driver, backend, budget=3)
        fill(driver, mapping)
        assert backend.stats.stop == "solved"
        assert backend.stats.macros_available == len(load(path).macros) > 0
        assert path.read_bytes() == before
        assert str(distinctive) not in json.dumps(json.loads(before)["macros"])
    assert isinstance(make_synthesizer("amaze"), AmazeSynthesizer)
    assert "stdlib" in synthesizer_label("amaze")


def test_missing_profile_and_unsupported_goal_are_controlled(tmp_path):
    driver = parse("def f : Int := ?h;")
    backend = AmazeSynthesizer(tmp_path / "absent.json")
    with pytest.raises(UnsupportedSynthesisGoal, match="profile unavailable"):
        backend.synthesize(driver.typing_ctx, t_int, lambda _: True, lambda _: [], Name("f", 0), {}, budget=0.1)
    from aeon.core.types import t_float

    with pytest.raises(UnsupportedSynthesisGoal, match="Int/Bool"):
        AmazeSynthesizer().synthesize(driver.typing_ctx, t_float, lambda _: True, lambda _: [], Name("f", 0), {})
    with pytest.raises(SynthesisNotSuccessful, match="budget"):
        AmazeSynthesizer().synthesize(
            driver.typing_ctx, t_int, lambda _: False, lambda _: [], Name("f", 0), {}, budget=0
        )


def test_cli_training_reload_and_actual_synthesis_with_project_overrides(tmp_path):
    output = tmp_path / "learned.json"
    (tmp_path / "Refinement.ae").write_text('def poison : Int := native "raise Exception()";')
    package_root = str(Path(__file__).resolve().parents[1])
    env = os.environ | {"PYTHONPATH": package_root, "AEONPATH": str(tmp_path)}
    trained = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon.synthesis.modules.amaze",
            "train-stdlib",
            "--output",
            str(output),
            "--budget",
            "30.0",
            "--task-budget",
            "0.3",
            "--max-candidates",
            "3000",
        ],
        cwd=tmp_path,
        env=env,
        text=True,
        capture_output=True,
        timeout=45,
    )
    assert trained.returncode == 0, trained.stdout + trained.stderr
    profile = load(output)
    assert all("poison" not in m.id for m in profile.macros)
    program = tmp_path / "test.ae"
    program.write_text("def inc (x:Int) : {v:Int | v = x + 1} := ?body;\ndef main (args:Int) : Int := inc 9;")
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--budget", "3", "-s", "amaze", str(program)],
        env=env | {"AEON_AMAZE_PROFILE": str(output)},
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=20,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_inference_really_consumes_the_learned_production(tmp_path):
    from aeon.typechecking.context import TypingContext
    from aeon.core.types import t_bool

    macros = load().macros
    selected = macros[0]
    variables = tuple(Name(f"input_{i}", 300 + i) for i in range(len(selected.arguments)))
    children = tuple(Expr("var", s, value=i) for i, s in enumerate(selected.arguments))
    wanted = instantiate(selected.template, children)
    base = Grammar(base_productions(selected.arguments))
    optimized = Grammar(base_productions(selected.arguments) + macros)
    assert optimized.rewrite_cost(wanted) < base.rewrite_cost(wanted)
    ctx = TypingContext()
    for name, sort in zip(variables, selected.arguments):
        ctx = ctx.with_var(name, t_int if sort == "Int" else t_bool)
    env = {n: e for n, e in zip(variables, children)}

    def accept(term):
        return from_core(term, env) == wanted

    backend = AmazeSynthesizer(max_cost=optimized.rewrite_cost(wanted))
    result = backend.synthesize(
        ctx, t_bool, accept, lambda _: [], Name("task", 400), {}, budget=3, ui=SilentSynthesisUI()
    )
    assert accept(result)
    payload = json.loads(DEFAULT_PROFILE.read_text())
    payload["selected"] = []
    baseline = tmp_path / "baseline.json"
    baseline.write_text(json.dumps(payload))
    with pytest.raises(SynthesisNotSuccessful, match="cost_limit"):
        AmazeSynthesizer(baseline, max_cost=optimized.rewrite_cost(wanted)).synthesize(
            ctx, t_bool, accept, lambda _: [], Name("task", 400), {}, budget=3, ui=SilentSynthesisUI()
        )


@pytest.mark.parametrize("payload", [None, [], {"schema": 1}, {"schema": "wrong"}])
def test_malformed_profile_fails_with_a_controlled_error(tmp_path, payload):
    path = tmp_path / "malformed.json"
    path.write_text(json.dumps(payload))
    with pytest.raises(ValueError):
        load(path)


def test_shared_objective_semantics_are_preserved():
    from aeon.synthesis.decorators import Goal
    from aeon.typechecking.context import TypingContext

    name = Name("maximize_value", 55)
    backend = AmazeSynthesizer(max_cost=3)
    result = backend.synthesize(
        TypingContext(),
        t_int,
        lambda _: True,
        lambda term: [float(evaluate(from_core(term, {}), ()))],
        name,
        {name: {"goals": [Goal(False, 1, Name("fitness", 66))]}},
        budget=2,
        ui=SilentSynthesisUI(),
    )
    assert evaluate(from_core(result, {}), ()) == 2
