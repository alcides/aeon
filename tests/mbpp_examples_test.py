"""Validates that every generated MBPP benchmark file parses and typechecks.

The files under ``examples/MBPP/`` are produced by ``scripts/generate_mbpp.py``
from the sanitized MBPP dataset. Each is a self-contained synthesis benchmark:
a ``native`` fitness function with the problem's assertions embedded, and a
``?hole`` synthesis target. This test only runs the parse/elaborate/typecheck
pipeline (no synthesis), so it stays fast while catching codegen regressions.
"""

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

MBPP_DIR = Path(__file__).parent.parent / "examples" / "MBPP"
MBPP_FILES = sorted(MBPP_DIR.glob("mbpp_*.ae"))


def test_mbpp_directory_is_populated():
    assert MBPP_FILES, f"no MBPP example files found in {MBPP_DIR}"


@pytest.mark.parametrize("path", MBPP_FILES, ids=lambda p: p.stem)
def test_mbpp_example_parses_and_typechecks(path: Path):
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
