"""Tests for import system and module resolution."""

import os
import tempfile
from pathlib import Path

import pytest

from aeon.compilation.resolve import clear_import_cache, get_package_libraries_dir, resolve_import
from aeon.sugar.program import ImportAe
from aeon.facade.api import ModuleNotFoundAeonError as AeonImportError


class TestPackageLibrariesDir:
    """Tests for get_package_libraries_dir helper."""

    def test_package_libraries_dir_exists(self):
        """Test that package libraries directory is found."""
        libs_dir = get_package_libraries_dir()
        assert libs_dir is not None
        assert libs_dir.exists()
        assert libs_dir.is_dir()
        assert libs_dir.name == "libraries"

    def test_standard_libraries_exist(self):
        """Test that standard library modules exist in package libraries."""
        libs_dir = get_package_libraries_dir()
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
        program = resolve_import(imp)
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
                program = resolve_import(imp)
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
            test_module = libs_dir / "LibMod.ae"
            test_module.write_text("def lib_func : Int := 99;")

            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                imp = ImportAe(module_path="LibMod")
                program = resolve_import(imp)
                assert program is not None
                def_names = [d.name.name for d in program.definitions]
                assert "lib_func" in def_names
            finally:
                os.chdir(old_cwd)

    def test_import_from_aeonpath(self):
        """Test importing from AEONPATH environment variable."""
        with tempfile.TemporaryDirectory() as tmpdir:
            custom_dir = Path(tmpdir) / "custom_libs"
            custom_dir.mkdir()
            test_module = custom_dir / "CustomMod.ae"
            test_module.write_text("def custom_func : Int := 123;")

            old_cwd = os.getcwd()
            old_aeonpath = os.environ.get("AEONPATH")
            try:
                os.chdir(tmpdir)
                os.environ["AEONPATH"] = str(custom_dir)
                imp = ImportAe(module_path="CustomMod")
                program = resolve_import(imp)
                assert program is not None
                def_names = [d.name.name for d in program.definitions]
                assert "custom_func" in def_names
            finally:
                os.chdir(old_cwd)
                if old_aeonpath is None:
                    os.environ.pop("AEONPATH", None)
                else:
                    os.environ["AEONPATH"] = old_aeonpath

    def test_import_precedence_cwd_over_package(self):
        """Test that cwd takes precedence over package libraries."""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create a Math.ae in cwd that shadows the package one
            test_module = Path(tmpdir) / "Math.ae"
            test_module.write_text("def shadowed : Int := 0;")

            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                imp = ImportAe(module_path="Math")
                program = resolve_import(imp)
                def_names = [d.name.name for d in program.definitions]
                assert "shadowed" in def_names
                assert "abs" not in def_names
            finally:
                os.chdir(old_cwd)

    def test_import_not_found_raises(self):
        """Test that importing a non-existent module raises an error."""
        imp = ImportAe(module_path="NonExistentModule12345")
        with pytest.raises(AeonImportError):
            resolve_import(imp)

    def test_import_caching(self):
        """Test that imports are cached by resolved file path."""
        with tempfile.TemporaryDirectory() as tmpdir:
            test_module = Path(tmpdir) / "CachedMod.ae"
            test_module.write_text("def cached : Int := 1;")

            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                imp = ImportAe(module_path="CachedMod")
                program1 = resolve_import(imp)
                program2 = resolve_import(imp)
                assert program1 is program2
            finally:
                os.chdir(old_cwd)

    def test_clear_import_cache(self):
        """Test that clear_import_cache forces re-parsing."""
        with tempfile.TemporaryDirectory() as tmpdir:
            test_module = Path(tmpdir) / "CacheClearMod.ae"
            test_module.write_text("def v1 : Int := 1;")

            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                imp = ImportAe(module_path="CacheClearMod")
                resolve_import(imp)
                test_module.write_text("def v2 : Int := 2;")
                clear_import_cache()
                program = resolve_import(imp)
                def_names = [d.name.name for d in program.definitions]
                assert "v2" in def_names
            finally:
                os.chdir(old_cwd)
