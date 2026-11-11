from __future__ import annotations

import hashlib
import pickle
from pathlib import Path

from importlib.metadata import version

from aeon.compilation.unit import AEC_FORMAT_VERSION, CompiledUnit

_COMPILER_VERSION = version("AeonLang")


def source_hash(contents: str) -> str:
    return hashlib.sha256(contents.encode("utf-8")).hexdigest()


def aec_path_for(source_path: str | Path) -> Path:
    path = Path(source_path)
    return path.with_suffix(".aec")


def is_cache_valid(unit: CompiledUnit, contents: str, dep_hashes: dict[str, str]) -> bool:
    if unit.format_version != AEC_FORMAT_VERSION:
        return False
    if unit.compiler_version != _COMPILER_VERSION:
        return False
    if unit.source_hash != source_hash(contents):
        return False
    return set(unit.dependencies) <= dep_hashes.keys() and unit.dependency_hashes() == dep_hashes


def write_unit(unit: CompiledUnit, source_path: str | Path) -> Path:
    path = aec_path_for(source_path)
    payload = pickle.dumps(unit, protocol=pickle.HIGHEST_PROTOCOL)
    path.write_bytes(payload)
    return path


def read_unit(source_path: str | Path) -> CompiledUnit | None:
    path = aec_path_for(source_path)
    if not path.exists():
        return None
    try:
        unit: CompiledUnit = pickle.loads(path.read_bytes())
    except Exception:
        return None
    if unit.format_version != AEC_FORMAT_VERSION:
        return None
    if unit.compiler_version != _COMPILER_VERSION:
        return None
    return unit
