"""Coverage accounting and typecheck-only CLI regressions."""

from pathlib import Path
import os
import subprocess
import sys

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from scripts.run_examples import (
    Example,
    ROOT,
    command_for,
    compilation_timeout,
    discover,
    environment_for,
    main,
    run_one,
    shard_for,
)


@pytest.mark.parametrize("count", [8, 16])
def test_recursive_discovery_and_shards_cover_every_example_once(count):
    examples = discover()
    paths = {example.path for example in examples}
    assert paths == {path.relative_to(ROOT).as_posix() for path in (ROOT / "examples").rglob("*.ae")}
    shards = [
        {example.path for example in examples if shard_for(example.path, count) == shard} for shard in range(count)
    ]
    assert set.union(*shards) == paths
    assert sum(map(len, shards)) == len(paths)
    assert all(shards)
    assert any("synthesis/srbench/" in path for path in paths)
    assert any("MBPP/" in path for path in paths)


def test_synthesis_examples_only_typecheck_even_with_example_annotations():
    for example in discover():
        if example.path.startswith("examples/synthesis/"):
            assert example.mode == "check"
            assert "--check" in command_for(example)
            assert "--test" not in command_for(example)


def test_property_examples_still_execute():
    examples = {example.path: example for example in discover()}
    assert examples["examples/pbt/props_basic.ae"].mode == "test"
    assert all(example.mode == "test" for path, example in examples.items() if path.startswith("examples/testing/"))


@pytest.mark.parametrize("control_code,passed", [(0, True), (1, False), (13, False)])
def test_open_proof_spec_requires_a_verified_control(monkeypatch, tmp_path, control_code, passed):
    commands = []
    codes = iter((13, control_code))

    def run(cmd, **kwargs):
        commands.append(cmd)
        return subprocess.CompletedProcess(cmd, next(codes))

    monkeypatch.setattr(subprocess, "run", run)
    example = Example("examples/synthesis/monotonicity/identity.ae", expected_codes=(13,), reference="x")
    result = run_one(example, 5, tmp_path)
    assert result["passed"] is passed
    assert "--check" in commands[0] and "--candidate" in commands[1]
    assert "--budget" not in commands[1]


def test_negative_examples_reject_only_compiler_diagnostics():
    negatives = [example for example in discover() if example.expected_codes != (0,)]
    assert len(negatives) >= 35
    assert all(1 not in example.expected_codes and 2 not in example.expected_codes for example in negatives)
    examples = {example.path: example for example in negatives}
    assert examples["examples/machine_learning/restrictions/00_linear_type_invalid.ae"].expected_codes == (12,)
    assert examples["examples/machine_learning/restrictions/08_train_test_roles_invalid.ae"].expected_codes == (5,)
    assert examples["examples/typestate/negative/coin_duplicate.ae"].expected_codes == (12,)


def test_suite_local_import_paths_preserve_existing_aeonpath(monkeypatch):
    monkeypatch.setenv("AEONPATH", "/custom/modules")
    env = environment_for(Example("examples/liquidhaskell/positive/list_map.ae"))
    assert env["AEONPATH"].split(os.pathsep) == [
        str(ROOT / "examples/liquidhaskell/positive"),
        str(ROOT / "examples/liquidhaskell"),
        str(ROOT / "examples"),
        "/custom/modules",
    ]


@pytest.mark.parametrize("code,passed", [(0, False), (1, False), (2, False), (5, True), (13, True)])
def test_runner_enforces_expected_diagnostic(monkeypatch, tmp_path, code, passed):
    monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: subprocess.CompletedProcess(args, code))
    result = run_one(Example("examples/negative.ae", expected_codes=(5, 13)), 1, tmp_path)
    assert result["passed"] is passed


def test_timeout_is_failure_even_for_negative_example(monkeypatch, tmp_path):
    def timeout(*args, **kwargs):
        raise subprocess.TimeoutExpired(args[0], 1)

    monkeypatch.setattr(subprocess, "run", timeout)
    result = run_one(Example("examples/negative.ae", expected_codes=(5, 13)), 1, tmp_path)
    assert result["timeout"] and not result["passed"]


@pytest.mark.parametrize("timeout", ["0", "-1", "nan", "inf"])
def test_runner_rejects_unbounded_or_invalid_timeout(monkeypatch, timeout):
    monkeypatch.setattr(sys, "argv", ["run_examples.py", "--timeout", timeout, "--list"])
    with pytest.raises(SystemExit) as error:
        main()
    assert error.value.code == 2


def test_source_size_budget_is_opt_in_and_capped():
    assert compilation_timeout(120, 14 * 1024 * 1024) == 120
    assert compilation_timeout(120, 1024 * 1024, 60, 600) == 180
    assert compilation_timeout(120, 14 * 1024 * 1024, 60, 600) == 600


@pytest.mark.parametrize(
    "flags",
    [
        ["--timeout-per-mib", "60"],
        ["--timeout-per-mib", "-1"],
        ["--timeout-per-mib", "nan"],
        ["--max-timeout", "inf"],
        ["--max-timeout", "100"],
    ],
)
def test_size_budget_cannot_disable_timeout_bound(monkeypatch, flags):
    monkeypatch.setattr(sys, "argv", ["run_examples.py", *flags, "--list"])
    with pytest.raises(SystemExit) as error:
        main()
    assert error.value.code == 2


def test_check_only_driver_never_prepares_execution_or_llvm(monkeypatch):
    def forbidden(*args, **kwargs):
        pytest.fail("Typechecking must not prepare execution or LLVM")

    monkeypatch.setattr("aeon.facade.driver.MultiBackendPipeline", forbidden)
    cfg = AeonConfig("tdsyn_enumerative", SilentSynthesisUI(), 1, no_main=True, check_only=True)
    driver = AeonDriver(cfg)
    assert not driver.parse(aeon_code="def f (x:Int) : Int := ?answer;")
    assert driver.core is not None


@pytest.mark.parametrize(
    "source,expected",
    [
        ("def f (x:Int) : Int := ?answer;", 0),
        ('def x : Int := native "1 / 0";', 0),
        ('def x : Int := "wrong";', 5),
        ("def x : {v:Int | v > 0} := -1;", 13),
        ("def x : Int := unknown_name;", 8),
    ],
)
def test_check_cli_does_not_synthesize_or_evaluate(tmp_path: Path, source, expected):
    path = tmp_path / "check.ae"
    path.write_text(source)
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--check", "--no-main", "--budget", "1", "-s", "invalid", str(path)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert result.returncode == expected, result.stdout + result.stderr


def test_proof_suite_expectations():
    examples = {example.path: example for example in discover()}
    for name in ("false_step", "false_goal", "circular_contract", "nonterminating"):
        assert examples[f"examples/proofs/negative/{name}.ae"].expected_codes == (13,)
    assert examples["examples/proofs/Paper.ae"].expected_codes == (0,)
    assert examples["examples/proofs/Paper.ae"].minimum_timeout == 600
