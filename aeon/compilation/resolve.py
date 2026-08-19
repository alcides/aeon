"""Resolve ``import`` paths to ``.ae`` source files and parse them."""

from __future__ import annotations

import os
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


def split_aeonpath() -> list[Path]:
    """Split ``AEONPATH`` using the platform path separator (``;`` on Windows)."""
    raw = os.environ.get("AEONPATH", "")
    if not raw:
        return []
    return [Path(s) for s in raw.split(os.pathsep) if s]


def import_search_containers() -> list[Path]:
    """Ordered import roots: cwd, ``cwd/libraries/``, package ``libraries/``, ``AEONPATH``."""
    seen: set[Path] = set()
    containers: list[Path] = []

    def add(path: Path) -> None:
        resolved = path.resolve()
        if resolved in seen:
            return
        seen.add(resolved)
        containers.append(path)

    add(Path.cwd())
    add(Path.cwd() / "libraries")

    pkg_libs = get_package_libraries_dir()
    if pkg_libs:
        add(pkg_libs)

    for entry in split_aeonpath():
        add(entry)

    return containers


def resolve_module_source(module_path: str) -> str | None:
    """Resolve a dotted module path (e.g. ``Math.Basic``) to an absolute ``.ae`` file."""
    rel = module_path.replace(".", "/") + ".ae"
    for container in import_search_containers():
        candidate = container / rel
        if candidate.exists():
            return str(candidate.resolve())
    return None


def resolve_import_path(imp: ImportAe) -> str | None:
    """Resolve an import to an absolute source file path, or ``None`` if not found."""
    return resolve_module_source(imp.module_path)


def resolve_import(imp: ImportAe) -> Program:
    """Parse a module referenced by ``imp``, using the standard search path."""
    resolved = resolve_import_path(imp)
    if resolved is None:
        raise ModuleNotFoundAeonError(importel=imp, possible_containers=import_search_containers())

    if resolved in _currently_importing:
        raise ModuleNotFoundAeonError(importel=imp, possible_containers=[Path.cwd()])

    if resolved in _import_cache:
        return _import_cache[resolved]

    _currently_importing.add(resolved)
    try:
        program = parse_main_program(Path(resolved).read_text(encoding="utf-8"), filename=resolved)
        _import_cache[resolved] = program
        return program
    finally:
        _currently_importing.discard(resolved)
