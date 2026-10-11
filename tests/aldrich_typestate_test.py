"""Attributed Aeon typestate models, with failing clients and passing controls."""

import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from aeon.errors import (
    LiquidTypeCheckingFailedRelation,
    LinearTypeNotBoundLinearlyError,
    LinearUnusedError,
    LinearUsedTooManyTimesError,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.facade.exit_codes import ExitCode
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.location import FileLocation

ROOT = Path(__file__).resolve().parents[1] / "examples" / "typestate"
MANIFEST = json.loads((ROOT / "manifest.json").read_text())
CASES = MANIFEST["cases"]
ERRORS = {
    "refinement": LiquidTypeCheckingFailedRelation,
    "unused": LinearUnusedError,
    "duplicate": LinearUsedTooManyTimesError,
    "unrestricted": LinearTypeNotBoundLinearlyError,
}


@pytest.fixture
def suite(tmp_path, monkeypatch):
    # Each test compiles independent paths; stale import caches cannot make a
    # broken library or client appear accepted.
    result = shutil.copytree(ROOT, tmp_path / "typestate")
    monkeypatch.setenv("AEONPATH", str(result))
    return result


def compile_case(suite, case):
    path = suite / case["file"]
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=not case.get("run", False)))
    errors = list(driver.parse(filename=str(path), aeon_code=path.read_text()))
    return driver, errors


def test_manifest_covers_every_case_and_cites_primary_sources():
    assert {c["file"] for c in CASES} == {
        str(p.relative_to(ROOT)) for folder in ("positive", "negative") for p in (ROOT / folder).glob("*.ae")
    }
    assert len({c["file"] for c in CASES}) == len(CASES)
    assert len(MANIFEST["papers"]) >= 3
    by_file = {c["file"]: c for c in CASES}
    for case in CASES:
        assert case["paper"] in MANIFEST["papers"]
        assert case["locator"] and case["adaptation"]
        if case["expect"] == "reject":
            control = by_file[case["control"]]
            assert control["expect"] == "accept"
            assert control["category"] == case["category"]
            assert case["error"] in ERRORS


def test_models_and_clients_have_no_trusted_proof_bodies_or_holes():
    for path in ROOT.rglob("*.ae"):
        source = "\n".join(line.split("#", 1)[0] for line in path.read_text().splitlines())
        assert all(word not in source for word in ("axiom", "native", "uninterpreted", "?")), path


@pytest.mark.parametrize("module", sorted(path.name for path in ROOT.glob("*.ae")))
def test_model_implementations_typecheck_independently(suite, module):
    _, errors = compile_case(suite, {"file": module})
    assert not errors, errors


@pytest.mark.parametrize("case", [c for c in CASES if c["expect"] == "accept"], ids=lambda c: c["file"])
def test_corrected_clients_compile_and_models_run(suite, case):
    driver, errors = compile_case(suite, case)
    assert not errors, errors
    assert not driver.has_synth()
    if case.get("run"):
        assert driver.run() == case["result"]


@pytest.mark.parametrize("case", [c for c in CASES if c["expect"] == "reject"], ids=lambda c: c["file"])
def test_bugs_are_rejected_statically_for_the_expected_reason(suite, case):
    _, errors = compile_case(suite, case)
    matching = [error for error in errors if isinstance(error, ERRORS[case["error"]])]
    assert matching, errors
    # Reject the client's protocol bug, not a broken imported model.
    for error in matching:
        loc = error.position()
        assert isinstance(loc, FileLocation), error
        assert Path(loc.file) == suite / case["file"], error


@pytest.mark.parametrize(
    "file,code",
    [
        ("positive/file_lifecycle.ae", ExitCode.SUCCESS),
        ("negative/file_read_closed.ae", ExitCode.CORE_TYPE_ERROR),
        ("negative/coin_loss.ae", ExitCode.LINEARITY_ERROR),
    ],
)
def test_documented_cli_examples(suite, file, code):
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", str(suite / file)],
        cwd=ROOT.parents[1],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == code, result.stdout + result.stderr
