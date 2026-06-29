"""Tests for per-module compilation units and .aec caching."""

from __future__ import annotations

from pathlib import Path

import pytest

from aeon.compilation.compile import clear_unit_cache, compile_file
from aeon.compilation.serialize import aec_path_for, read_unit
from aeon.compilation.unit import AEC_FORMAT_VERSION
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


@pytest.fixture(autouse=True)
def _clear_caches():
    clear_unit_cache()
    yield
    clear_unit_cache()


def test_compile_math_unit():
    path = Path("aeon/libraries/Math.ae").resolve()
    unit, errors = compile_file(str(path), is_main=False)
    assert errors == []
    assert unit.module_path == "Math"
    assert "abs" in unit.exports
    assert unit.exports["abs"].internal_name.name == "Math_abs"
    assert unit.format_version == AEC_FORMAT_VERSION


def test_aec_cache_written_and_reloaded(tmp_path, monkeypatch):
    src = tmp_path / "Lib.ae"
    src.write_text("def value : Int := 7;\n")
    unit1, errors1 = compile_file(str(src), is_main=False, write_cache=True)
    assert errors1 == []
    cache = aec_path_for(src)
    assert cache.exists()
    clear_unit_cache()
    unit2 = read_unit(src)
    assert unit2 is not None
    assert unit2.source_hash == unit1.source_hash
    assert unit2.exports["value"].internal_name.name == "Lib_value"


def test_imported_program_via_driver(tmp_path, monkeypatch):
    lib = tmp_path / "Counter.ae"
    lib.write_text("def inc (n:Int) : Int := n + 1;\n")
    main = tmp_path / "Main.ae"
    main.write_text("import Counter;\ndef main (u:Int) : Int := Counter.inc 41;\n")
    monkeypatch.chdir(tmp_path)
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    assert driver.parse(filename=str(main)) == []
    assert driver.run() == 42
