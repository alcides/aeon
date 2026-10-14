"""Compile PSB2 synthesis examples without fetching datasets or running search."""

from __future__ import annotations

import contextlib
import io
from pathlib import Path

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

# Registers the custom "TIME" log level that the driver's RecordTime uses.
setup_logger()

PSB2_DIR = Path(__file__).parent.parent / "examples" / "PSB2"
PSB2_FILES = sorted(p for p in PSB2_DIR.rglob("*.ae") if "solved" not in p.parts)


def test_psb2_directory_is_populated():
    assert PSB2_FILES, f"no PSB2 example files found in {PSB2_DIR}"


@pytest.mark.parametrize("path", PSB2_FILES, ids=lambda p: p.stem)
def test_psb2_example_parses_and_typechecks(path: Path):
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    driver = AeonDriver(cfg)
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        errors = driver.parse(str(path))
    assert not errors, f"{path.name} failed to typecheck: {errors}"
    assert driver.has_synth(), f"{path.name} has no synthesis hole"
