"""Resolve ``import`` paths to ``.ae`` source files and parse them."""

from __future__ import annotations

from pathlib import Path

import aeon
from aeon.facade.api import ModuleNotFoundAeonError
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import ImportAe, Program

_import_cache: dict[str, Program] = {}
_currently_importing: set[str] = set()


def clear_import_cache() -> None:
    """Clear the import parse cache. Useful for tests and LSP reloads."""
    _import_cache.clear()
    _currently_importing.clear()


def get_package_libraries_dir() -> Path | None:
    """Return the path to the libraries directory shipped inside the aeon package."""
    try:
        aeon_package_dir = Path(aeon.__file__).parent
        candidates = [
            aeon_package_dir / "libraries",
            aeon_package_dir.parent / "libraries",
        ]
        for libraries_dir in candidates:
            if libraries_dir.exists() and libraries_dir.is_dir():
                return libraries_dir
    except Exception:
        pass
    return None


def resolve_import_path(imp: ImportAe) -> str | None:
    """Resolve an import to an absolute source file path, or ``None`` if not found."""
    path = imp.file_path
    possible_containers = [Path.cwd(), Path.cwd() / "libraries"]
    pkg_libs = get_package_libraries_dir()
    if pkg_libs:
        possible_containers.append(pkg_libs)
    import os

    aeonpath = os.environ.get("AEONPATH", "")
    if aeonpath:
        possible_containers.extend(Path(s) for s in aeonpath.split(";") if s)
    for container in possible_containers:
        file = container / path
        if file.exists():
            return str(file.resolve())
    return None


def resolve_import(imp: ImportAe) -> Program:
    """Parse a module referenced by ``imp``, using the standard search path."""
    resolved = resolve_import_path(imp)
    if resolved is None:
        possible_containers = [Path.cwd(), Path.cwd() / "libraries"]
        pkg_libs = get_package_libraries_dir()
        if pkg_libs:
            possible_containers.append(pkg_libs)
        raise ModuleNotFoundAeonError(importel=imp, possible_containers=possible_containers)

    if resolved in _currently_importing:
        possible_containers = [Path.cwd()]
        raise ModuleNotFoundAeonError(importel=imp, possible_containers=possible_containers)

    if resolved in _import_cache:
        return _import_cache[resolved]

    _currently_importing.add(resolved)
    try:
        program = parse_main_program(Path(resolved).read_text(encoding="utf-8"), filename=resolved)
        _import_cache[resolved] = program
        return program
    finally:
        _currently_importing.discard(resolved)
