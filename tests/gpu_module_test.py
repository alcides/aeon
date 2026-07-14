"""GPU module is scoped to ``@gpu`` / ``open Gpu``, not the global prelude."""

from __future__ import annotations

import tempfile

from aeon.compilation.compile import clear_unit_cache, compile_and_link_program
from aeon.elaboration.context import (
    ElabTypeDecl,
    ElabTypeVarBinder,
    ElabUninterpretedBinder,
    ElabVariableBinder,
)
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program


def _typing_names(source: str) -> set[str]:
    desugared = desugar(parse_program(source))
    names: set[str] = set()
    for entry in desugared.elabcontext.entries:
        match entry:
            case ElabVariableBinder(name=name) | ElabUninterpretedBinder(name=name):
                names.add(name.name)
            case ElabTypeDecl(name=name) | ElabTypeVarBinder(name=name):
                names.add(name.name)
    return names


def _compile_errors(source: str) -> list[str]:
    clear_unit_cache()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".ae", delete=False, encoding="utf-8") as tmp:
        tmp.write(source)
        path = tmp.name
    _, _, _, _, _, errors = compile_and_link_program(source, filename=path, is_main=True)
    return [str(e) for e in (errors or [])]


def test_gpu_builtins_not_in_prelude():
    prelude_names = {name.name for name in typing_vars}
    for gpu_name in ("gpu_map", "gpu_imap", "gpu_reduce", "gpu_filter", "gpu_dot", "run_gpu"):
        assert gpu_name not in prelude_names


def test_gpu_functions_unavailable_without_import():
    source = """
        def main (args:Int) : Int := gpu_map;
    """
    errors = _compile_errors(source)
    assert any("gpu_map" in err and "does not exist" in err for err in errors)


def test_gpu_decorator_imports_gpu_module():
    source = """
        @gpu
        def kernel (a:Int) (b:Int) : Int := a + b;

        def main (args:Int) : Int := gpu_map;
    """
    assert "GpuConfig" in _typing_names(source)
    errors = _compile_errors(source)
    assert errors
    assert not any("gpu_map" in err and "does not exist" in err for err in errors)


def test_open_gpu_makes_functions_available():
    source = """
        open Gpu

        def main (args:Int) : Int := gpu_map;
    """
    assert "GpuConfig" in _typing_names(source)
    errors = _compile_errors(source)
    assert errors
    assert not any("gpu_map" in err and "does not exist" in err for err in errors)


def test_gpu_decorator_does_not_duplicate_import():
    source = """
        open Gpu

        @gpu
        def kernel (a:Int) (b:Int) : Int := a + b;

        def main (args:Int) : Int := 0;
    """
    errors = _compile_errors(source)
    assert errors == []


def test_non_gpu_program_has_no_gpu_context():
    source = """
        def main (args:Int) : Int := args + 1;
    """
    names = _typing_names(source)
    assert "GpuConfig" not in names
    assert not any("gpu" in name.lower() for name in names)
