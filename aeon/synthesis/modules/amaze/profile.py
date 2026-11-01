"""Versioned data-only profiles; inference can load but cannot update them."""

from __future__ import annotations

from dataclasses import dataclass
import json
import math
from pathlib import Path

from .corpus import digest, source_inventory
from .grammar import FEATURE_VERSION, GRAMMAR_VERSION, SIGNATURES, Production
from .mining import production

DEFAULT_PROFILE = Path(__file__).with_name("stdlib-profile.json")
MAX_PROFILE_BYTES = 4 * 1024 * 1024


@dataclass(frozen=True)
class Profile:
    sha256: str
    stdlib_sha256: str
    macros: tuple[Production, ...]
    # The manifest/model remain immutable, including nested data. A caller
    # wanting a report can deserialize a fresh copy of this canonical string.
    document: str


def save(path: Path, payload):
    payload = dict(payload)
    payload["primitive_signatures"] = SIGNATURES
    text = json.dumps(payload, sort_keys=True, indent=2, allow_nan=False) + "\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(text)
    temporary.replace(path)


def load(path: Path = DEFAULT_PROFILE) -> Profile:
    try:
        return _load(path)
    except (KeyError, TypeError, AttributeError, IndexError) as exc:
        raise ValueError("malformed AMaze profile; expected the versioned stdlib training schema") from exc


def _load(path: Path) -> Profile:
    try:
        if path.stat().st_size > MAX_PROFILE_BYTES:
            raise ValueError("profile exceeds size limit")
        data = path.read_bytes()
    except OSError as exc:
        raise ValueError(
            "AMaze profile unavailable; run python -m aeon.synthesis.modules.amaze train-stdlib --output <profile>"
        ) from exc
    doc = json.loads(data)
    if (
        doc.get("schema") != 1
        or doc.get("grammar_version") != GRAMMAR_VERSION
        or doc.get("feature_version") != FEATURE_VERSION
    ):
        raise ValueError("incompatible AMaze schema/grammar/rank version; retrain from the installed stdlib")
    if doc.get("primitive_signatures") != json.loads(json.dumps(SIGNATURES)):
        raise ValueError("incompatible fixed primitive grammar")
    inventory = source_inventory()
    expected = {p: v["sha256"] for p, v in doc["corpus"]["files"].items()}
    actual = {p: v["sha256"] for p, v in inventory["files"].items()}
    if actual != expected:
        raise ValueError("stale AMaze stdlib profile: source inventory/hashes changed; explicitly retrain")
    # Historical canonical roots may move across installs; relative paths and
    # hashes must match the CURRENT canonical package tree, including symlinks.
    old_root = Path(doc["corpus"]["root"])
    if not old_root.is_absolute() or any(
        not Path(v["canonical_path"]).is_relative_to(old_root) for v in doc["corpus"]["files"].values()
    ):
        raise ValueError("invalid source lineage outside recorded stdlib root")
    tasks = {t["id"]: t for t in doc["corpus"]["tasks"]}
    if not tasks or {t["split"] for t in tasks.values()} != {"train", "validation", "held_out"}:
        raise ValueError("missing stdlib train/validation/held-out splits")
    for task in tasks.values():
        if task["source"] not in actual or task["source_sha256"] != actual[task["source"]]:
            raise ValueError("training task has invalid source provenance")
    for dependencies in doc["corpus"]["dependencies"].values():
        if any(path not in actual or actual[path] != checksum for path, checksum in dependencies.items()):
            raise ValueError("dependency has invalid stdlib provenance")
    records = doc["macros"]
    if len(records) > 128 or len(doc["selected"]) > 16:
        raise ValueError("profile production limit exceeded")
    macros = {}
    for record in records:
        origins = record["origins"]
        if not origins or any(t not in tasks or tasks[t]["split"] != "train" for t in origins):
            raise ValueError("macro lineage must refer only to stdlib training functions")
        if record["id"] in macros:
            raise ValueError("duplicate macro ID")
        macros[record["id"]] = production(record)
    for label in doc["labels"]:
        if label["task"] not in tasks or tasks[label["task"]]["split"] != "train":
            raise ValueError("cost-model label outside stdlib training split")
        if label.get("source_sha256") != tasks[label["task"]]["source_sha256"] and label["status"] != "global_budget":
            raise ValueError("training label source hash mismatch")
    for key in ("cost_model", "runtime_model"):
        if any(
            not isinstance(doc[key][k], (int, float)) or not math.isfinite(doc[key][k])
            for k in ("intercept", "slope", "ridge")
        ):
            raise ValueError("invalid fitted model")
    selected = doc["selected"]
    if len(set(selected)) != len(selected) or any(i not in macros for i in selected):
        raise ValueError("invalid selected productions")
    return Profile(
        digest(data),
        digest(json.dumps(actual, sort_keys=True).encode()),
        tuple(macros[i] for i in selected),
        data.decode(),
    )
