"""Tests for import system and module resolution."""

import os
import tempfile
from pathlib import Path

import pytest

from aeon.sugar.desugar import _get_package_libraries_dir, _resolve_import, clear_import_cache
from aeon.sugar.program import ImportAe
from aeon.sugar.parser import mk_parser
from aeon.facade.api import ImportError as AeonImportError


class TestPackageLibrariesDir:
    """Tests for _get_package_libraries_dir helper."""

    def test_package_libraries_dir_exists(self):
        """Test that package libraries directory is found."""
        libs_dir = _get_package_libraries_dir()
        assert libs_dir is not None
        assert libs_dir.exists()
        assert libs_dir.is_dir()
        assert libs_dir.name == "libraries"

    def test_standard_libraries_exist(self):
        """Test that standard library modules exist in package libraries."""
        libs_dir = _get_package_libraries_dir()
        assert libs_dir is not None

        # Check for common standard library modules
        assert (libs_dir / "List.ae").exists()
        assert (libs_dir / "Math.ae").exists()
        assert (libs_dir / "Array.ae").exists()


class TestImportResolution:
    """Tests for import resolution and search path order."""

    def setup_method(self):
        """Clear import cache before each test."""
        clear_import_cache()

    def teardown_method(self):
        """Clear import cache after each test."""
        clear_import_cache()

    def test_import_from_package_libraries(self):
        """Test importing a standard library module."""
        imp = ImportAe(module_path="Math")
        program = _resolve_import(imp)
        assert program is not None
        # Check that Math module has expected definitions
        def_names = [d.name.name for d in program.definitions]
        assert "abs" in def_names

    def test_import_from_cwd(self):
        """Test importing a module from current working directory."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create a test module in tmpdir
            test_module = Path(tmpdir) / "TestMod.ae"
            test_module.write_text("def test_func : Int := 42;")

            # Change to tmpdir and try to import
            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                imp = ImportAe(module_path="TestMod")
                program = _resolve_import(imp)
                assert program is not None
                def_names = [d.name.name for d in program.definitions]
                assert "test_func" in def_names
            finally:
                os.chdir(old_cwd)

    def test_import_from_cwd_libraries(self):
        """Test importing from cwd/libraries subdirectory."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create libraries subdirectory with a module
            libs_dir = Path(tmpdir) / "libraries"
            libs_dir.mkdir()
            test_module = libs_dir / "LocalLib.ae"
            test_module.write_text("def local_func : Int := 123;")

            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                imp = ImportAe(module_path="LocalLib")
                program = _resolve_import(imp)
                assert program is not None
                def_names = [d.name.name for d in program.definitions]
                assert "local_func" in def_names
            finally:
                os.chdir(old_cwd)

    def test_import_from_aeonpath(self):
        """Test importing from AEONPATH environment variable."""
        with tempfile.TemporaryDirectory() as tmpdir:
            custom_lib = Path(tmpdir) / "CustomLib.ae"
            custom_lib.write_text("def custom_func : Int := 999;")

            old_aeonpath = os.environ.get("AEONPATH")
            try:
                os.environ["AEONPATH"] = tmpdir
                imp = ImportAe(module_path="CustomLib")
                program = _resolve_import(imp)
                assert program is not None
                def_names = [d.name.name for d in program.definitions]
                assert "custom_func" in def_names
            finally:
                if old_aeonpath is None:
                    os.environ.pop("AEONPATH", None)
                else:
                    os.environ["AEONPATH"] = old_aeonpath

    def test_import_precedence_cwd_over_package(self):
        """Test that cwd takes precedence over package libraries."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create a local Math.ae that shadows the standard library
            local_math = Path(tmpdir) / "Math.ae"
            local_math.write_text("def shadow_func : Int := 555;")

            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                imp = ImportAe(module_path="Math")
                program = _resolve_import(imp)
                assert program is not None
                def_names = [d.name.name for d in program.definitions]
                # Should have the local version, not the standard library
                assert "shadow_func" in def_names
                assert "abs" not in def_names  # Standard library Math has abs
            finally:
                os.chdir(old_cwd)

    def test_import_nonexistent_module_error(self):
        """Test that importing a non-existent module raises ImportError."""
        imp = ImportAe(module_path="NonExistentModule")
        with pytest.raises(AeonImportError) as exc_info:
            _resolve_import(imp)
        assert "NonExistentModule" in str(exc_info.value)
        assert "NonExistentModule.ae" in str(exc_info.value)

    def test_import_nested_module_path(self):
        """Test importing nested module paths (e.g., Foo.Bar -> Foo/Bar.ae)."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create nested directory structure
            foo_dir = Path(tmpdir) / "Foo"
            foo_dir.mkdir()
            bar_module = foo_dir / "Bar.ae"
            bar_module.write_text("def nested_func : Int := 777;")

            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                imp = ImportAe(module_path="Foo.Bar")
                program = _resolve_import(imp)
                assert program is not None
                def_names = [d.name.name for d in program.definitions]
                assert "nested_func" in def_names
            finally:
                os.chdir(old_cwd)

    def test_import_caching(self):
        """Test that imports are cached and reused."""
        imp = ImportAe(module_path="Math")
        program1 = _resolve_import(imp)
        program2 = _resolve_import(imp)
        # Should be the same object (cached)
        assert program1 is program2


class TestEndToEndImports:
    """End-to-end tests for imports in actual aeon programs."""

    def setup_method(self):
        """Clear import cache before each test."""
        clear_import_cache()

    def teardown_method(self):
        """Clear import cache after each test."""
        clear_import_cache()

    def test_parse_program_with_stdlib_import(self):
        """Test parsing a program that imports from stdlib."""
        source = """
import Math;

def main (args: Int): Unit :=
    print (Math.abs (0 - 5));
"""
        parser = mk_parser("program")
        program = parser(source)
        assert program is not None
        assert len(program.imports) == 1
        assert program.imports[0].module_path == "Math"

    def test_parse_program_with_open_import(self):
        """Test parsing a program with open import."""
        source = """
open Math

def main (args: Int): Unit :=
    print (abs 5);
"""
        parser = mk_parser("program")
        program = parser(source)
        assert program is not None
        assert len(program.imports) == 1
        assert program.imports[0].module_path == "Math"
        assert program.imports[0].is_open

    def test_parse_program_with_selective_import(self):
        """Test parsing a program with selective import."""
        source = """
import Math (abs, pow)

def main (args: Int): Unit :=
    print (abs (0 - 5));
"""
        parser = mk_parser("program")
        program = parser(source)
        assert program is not None
        assert len(program.imports) == 1
        assert program.imports[0].module_path == "Math"
        assert program.imports[0].selected_names == ["abs", "pow"]
