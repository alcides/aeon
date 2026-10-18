"""DENSER examples use the packaged grammar through ordinary imports."""

from pathlib import Path

import pytest

from aeon.compilation.resolve import resolve_module_source
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


@pytest.mark.parametrize("task", ["mnist", "cifar10", "smoke"])
def test_denser_tasks_compile_without_aeonpath(task, tmp_path, monkeypatch):
    source = Path(__file__).resolve().parents[1] / "examples/synthesis/denser" / f"{task}.ae"
    monkeypatch.delenv("AEONPATH", raising=False)
    monkeypatch.chdir(tmp_path)
    assert resolve_module_source("Denser") is not None
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 1, no_main=True, check_only=True))
    assert list(driver.parse(filename=str(source))) == []
