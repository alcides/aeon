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


def test_import_alias_is_a_qualified_source_name(tmp_path, monkeypatch):
    lib = tmp_path / "Counter.ae"
    lib.write_text("def inc (n:Int) : Int := n + 1;\n")
    main = tmp_path / "Main.ae"
    main.write_text("import Counter as C;\ndef main (u:Int) : Int := C.inc 41;\n")
    monkeypatch.chdir(tmp_path)
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    assert driver.parse(filename=str(main)) == []
    assert driver.run() == 42


def test_nested_namespace_is_a_qualified_source_name():
    source = """
namespace Data.List
  def zero : Int := 0;
end

def main (u:Int) : Int := Data.List.zero;
"""
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    assert driver.parse(aeon_code=source, filename="<namespace>") == []
    assert driver.run() == 0


def test_namespace_declarations_resolve_siblings_unqualified():
    source = """
namespace Data.List
  def zero : Int := 0;
  def one : Int := zero + 1;
end
def main (u:Int) : Int := Data.List.one;
"""
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    assert driver.parse(aeon_code=source, filename="<namespace-siblings>") == []
    assert driver.run() == 1


def test_private_definition_is_not_exported(tmp_path):
    lib = tmp_path / "Secrets.ae"
    lib.write_text("private def secret : Int := 7;\ndef public : Int := secret;\n")
    unit, errors = compile_file(str(lib), is_main=False, write_cache=False)
    assert errors == []
    assert "public" in unit.exports
    assert "secret" not in unit.exports


def test_explicit_export_list_limits_a_module_interface(tmp_path):
    lib = tmp_path / "Interface.ae"
    lib.write_text("def shown : Int := 1;\ndef hidden : Int := 2;\nexport (shown);\n")
    unit, errors = compile_file(str(lib), is_main=False, write_cache=False)
    assert errors == []
    assert set(unit.exports) == {"shown"}


def test_reexport_is_visible_through_the_reexporting_module(tmp_path, monkeypatch):
    (tmp_path / "A.ae").write_text("def value : Int := 41;\n")
    (tmp_path / "B.ae").write_text("import A;\nexport A (value);\n")
    main = tmp_path / "Main.ae"
    main.write_text("import B;\ndef main (u:Int) : Int := B.value + 1;\n")
    monkeypatch.chdir(tmp_path)
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    assert driver.parse(filename=str(main)) == []
    assert driver.run() == 42


def test_opened_name_collision_requires_qualification(tmp_path, monkeypatch):
    (tmp_path / "Left.ae").write_text("def shared : Int := 1;\n")
    (tmp_path / "Right.ae").write_text("def shared : Int := 2;\n")
    main = tmp_path / "Main.ae"
    main.write_text("open Left;\nopen Right;\ndef main (u:Int) : Int := shared;\n")
    monkeypatch.chdir(tmp_path)
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    errors = driver.parse(filename=str(main))
    assert len(errors) == 1
    assert "Ambiguous unqualified name 'shared'" in str(errors[0])


def test_qualified_type_from_source_namespace():
    source = """
namespace Domain
  type Token;
end
def keep (x: Domain.Token) : Domain.Token := x;
"""
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    assert driver.parse(aeon_code=source, filename="<qualified-type>") == []


def test_refinement_standard_library_predicates_are_usable_qualified():
    source = """
import Refinement;
def int_identity (x: {v:Int | Refinement.non_negative v}) :
    {v:Int | Refinement.non_negative v} := x;
def float_identity (x: {v:Float | Refinement.positive_float v}) :
    {v:Float | Refinement.positive_float v} := x;
"""
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    assert driver.parse(aeon_code=source, filename="<refinement-stdlib>") == []


def test_nested_module_path_is_its_canonical_identity(tmp_path, monkeypatch):
    package = tmp_path / "Pkg"
    package.mkdir()
    lib = package / "Counter.ae"
    lib.write_text("def inc (n:Int) : Int := n + 1;\n")
    main = tmp_path / "Main.ae"
    main.write_text("import Pkg.Counter;\ndef main (u:Int) : Int := Pkg.Counter.inc 41;\n")
    monkeypatch.chdir(tmp_path)
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    assert driver.parse(filename=str(main)) == []
    assert driver.run() == 42
    unit, errors = compile_file(str(lib), is_main=False, write_cache=False, module_path="Pkg.Counter")
    assert errors == []
    assert unit.module_path == "Pkg.Counter"
    assert unit.exports["inc"].internal_name.name == "Pkg_Counter_inc"
