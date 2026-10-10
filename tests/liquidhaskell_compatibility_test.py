"""Executable, attributed LiquidHaskell ports and explicit Aeon boundaries."""

import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from aeon.errors import ContractViolationError, LiquidTypeCheckingFailedRelation, UnreachablePatternError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.facade.exit_codes import ExitCode
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.location import FileLocation
from aeon.verification.constructor_registry import clear_constructor_registry
from aeon.verification.smt import clear_smt_caches

ROOT = Path(__file__).resolve().parents[1] / "examples" / "liquidhaskell"
MANIFEST = json.loads((ROOT / "manifest.json").read_text())
CASES = MANIFEST["cases"]


@pytest.fixture
def suite(tmp_path, monkeypatch):
    # Independent source paths avoid accepting results from persistent caches.
    clear_constructor_registry()
    clear_smt_caches()
    result = shutil.copytree(ROOT, tmp_path / "suite")
    monkeypatch.setenv("AEONPATH", str(result))
    yield result
    clear_constructor_registry()
    clear_smt_caches()


def compile_case(suite, case, *, contracts=False):
    path = suite / case["file"]
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, contracts=contracts))
    errors = list(driver.parse(filename=str(path), aeon_code=path.read_text()))
    return driver, errors


def test_manifest_is_complete_and_attributed():
    assert len({case["file"] for case in CASES}) == len(CASES)
    assert {case["file"] for case in CASES} == {
        str(path.relative_to(ROOT))
        for folder in ("positive", "negative", "runtime")
        for path in (ROOT / folder).glob("*.ae")
    }
    assert {case["category"] for case in CASES} >= {
        "arithmetic",
        "adts",
        "recursion",
        "measures",
        "ffi",
        "inference",
        "diagnostics",
    }
    assert len(MANIFEST["upstream_revision"]) == 40
    for case in CASES:
        assert case["upstream_file"] and case["symbol"] and case["adaptation"]
        assert case["stability"] in {"stable", "experimental", "research"}
        assert case["kind"] in {"port", "mutation", "aeon-companion"}
        assert case["expect"] in {"accept", "reject", "runtime-reject"}


@pytest.mark.parametrize(
    "feature", ["polymorphism", "higher-order", "richer-measures", "sorted-lists", "abstract-refinements"]
)
def test_advanced_features_have_executable_ports_and_negative_controls(feature):
    cases = [case for case in CASES if case.get("feature") == feature]
    assert {case["expect"] for case in cases} >= {"accept", "reject"}
    for case in cases:
        # These examples must be Aeon implementations, not trusted Python
        # specifications or uninterpreted proof helpers that assert the goal.
        source = (ROOT / case["file"]).read_text()
        assert "native" not in source and "uninterpreted" not in source


@pytest.mark.parametrize("case", [c for c in CASES if c["expect"] == "accept"], ids=lambda c: c["file"])
@pytest.mark.parametrize("contracts", [False, True], ids=["static", "runtime-verification"])
def test_positive_ports_compile_and_run(suite, case, contracts):
    driver, errors = compile_case(suite, case, contracts=contracts)
    assert not errors, errors
    assert not driver.has_synth(), "A port must not leave term holes unresolved"
    assert driver.run() == case["result"]


@pytest.mark.parametrize("case", [c for c in CASES if c["expect"] == "reject"], ids=lambda c: c["file"])
def test_negative_ports_fail_for_the_intended_reason(suite, case):
    _, errors = compile_case(suite, case)
    expected = {"refinement": LiquidTypeCheckingFailedRelation, "unreachable": UnreachablePatternError}[case["error"]]
    matching = [e for e in errors if isinstance(e, expected)]
    assert matching, errors
    for error in matching:
        loc = error.position()
        assert isinstance(loc, FileLocation)
        assert Path(loc.file) == suite / case["file"]
        assert 1 <= loc.start[0] <= len((suite / case["file"]).read_text().splitlines())
        if case["file"] == "negative/sorted_loop.ae":
            assert loc.start[0] == 9, "Report the non-decreasing call, not the imported constructor"
    if case["category"] == "diagnostics":
        assert matching[0].failed_predicate() is not None
        assert bool(matching[0].counterexample()) == case["counterexample"]


@pytest.mark.parametrize("case", [c for c in CASES if c["expect"] == "runtime-reject"], ids=lambda c: c["file"])
def test_native_implementation_is_trusted_not_statically_proved(suite, case):
    unchecked, errors = compile_case(suite, case)
    assert not errors, errors
    assert unchecked.run() == case["unchecked_result"]
    checked, errors = compile_case(suite, case, contracts=True)
    assert not errors, errors
    with pytest.raises(ContractViolationError) as exc:
        checked.run()
    assert exc.value.blame == "callee"


@pytest.mark.parametrize(
    "file,flags,code",
    [
        ("positive/list_map.ae", [], ExitCode.SUCCESS),
        ("negative/singleton.ae", [], ExitCode.CORE_TYPE_ERROR),
        ("positive/native_absolute.ae", ["--runtime-verification"], ExitCode.SUCCESS),
    ],
)
def test_documented_cli_contract(suite, file, flags, code):
    result = subprocess.run(
        [sys.executable, "-m", "aeon", *flags, str(suite / file)],
        cwd=ROOT.parents[1],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == code, result.stdout + result.stderr
