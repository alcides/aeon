"""Regenerate the corpus: python -m scripts.paper_benchmarks --help."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import shutil
import tarfile
import urllib.request
import zipfile
from pathlib import Path, PurePosixPath

from .common import Corpus
from .contest import asac
from .elm import smyth
from .examples import dreamcoder, l2
from .invariants import clause2inv
from .memoization import synmem
from .ml import ml_suites
from .para import para
from .queries import hectare, hoogle

ROOT = Path(__file__).resolve().parents[2]
PINS = Path(__file__).with_name("sources.json")
GENERATORS = {
    "l2": l2,
    "smyth": smyth,
    "dreamcoder": dreamcoder,
    "asac": asac,
    "clause2inv": clause2inv,
    "para": para,
    "hoogle": hoogle,
    "hectare": hectare,
    "synmem": synmem,
}
ML_SUITES = {"burst", "trio", "trio-jfp", "guide"}


def file_hash(path):
    checksum = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            checksum.update(chunk)
    return checksum.hexdigest()


def safe_relative(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"Unsafe archive member: {name}")
    return Path(*path.parts)


def write_member(root, name, stream):
    destination = root / safe_relative(name)
    # Never follow a pre-existing symlink in the output tree.
    if any(p.is_symlink() for p in [destination, *destination.parents]):
        raise ValueError(f"Symlink in destination: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("wb") as output:
        shutil.copyfileobj(stream, output)


def extract_archive(archive, destination, kind="tar"):
    if destination.is_symlink() or any(p.is_symlink() for p in destination.rglob("*")):
        raise ValueError(f"Unsafe pre-existing symlink in destination: {destination}")
    if kind == "zip":
        with zipfile.ZipFile(archive) as bundle:
            for member in bundle.infolist():
                relative = safe_relative(member.filename)
                if member.is_dir() or len(relative.parts) < 2:
                    continue
                with bundle.open(member) as source:
                    write_member(destination, relative.relative_to(relative.parts[0]).as_posix(), source)
        return
    with tarfile.open(archive) as bundle:
        if kind == "docker":
            manifest = json.load(bundle.extractfile("manifest.json"))
            files = {}
            for layer in manifest[0]["Layers"]:
                layer_files = {}
                with tarfile.open(fileobj=bundle.extractfile(safe_relative(layer).as_posix())) as content:
                    for member in content:
                        if not member.name.startswith("home/SynMem/") or not member.isfile():
                            continue
                        relative = safe_relative(member.name[len("home/SynMem/") :])
                        if relative.name.startswith(".wh."):
                            # Apply Docker deletions in memory, in manifest order;
                            # never interpret a whiteout as a specification file.
                            parent = relative.parent.as_posix()
                            prefix = "" if parent == "." else parent + "/"
                            if relative.name == ".wh..wh..opq":
                                files = {name: data for name, data in files.items() if not name.startswith(prefix)}
                            else:
                                target = prefix + relative.name[len(".wh.") :]
                                files = {
                                    name: data
                                    for name, data in files.items()
                                    if name != target and not name.startswith(target + "/")
                                }
                            continue
                        if relative.parts[0] in ("benchmarks", "src") or relative.name in (
                            "README.md",
                            "run_experiment.py",
                        ):
                            layer_files[relative.as_posix()] = content.extractfile(member).read()
                files.update(layer_files)
            for name, data in files.items():
                write_member(destination, name, io.BytesIO(data))
            return
        links = []
        for member in bundle:
            relative = safe_relative(member.name)
            if len(relative.parts) < 2:
                continue
            relative = relative.relative_to(relative.parts[0])
            if member.isfile():
                write_member(destination, relative.as_posix(), bundle.extractfile(member))
            elif member.issym():
                links.append((relative, member.linkname))
        # Smyth's shared sketch directories are relative internal symlinks.
        # Materialize copies only after checking that their target stays inside.
        for relative, target in links:
            source = (destination / relative.parent / target).resolve()
            if not source.is_relative_to(destination.resolve()):
                raise ValueError(f"Unsafe archive symlink: {relative} -> {target}")
            dest = destination / relative
            if source.is_dir():
                shutil.copytree(source, dest, dirs_exist_ok=True)
            elif source.is_file():
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, dest)
            # Several repositories link to unbuilt executables or separately
            # downloaded datasets. Leave those absent; translators themselves
            # require every specification/sketch they actually consume.


def fetch_sources(root, selected):
    root.mkdir(parents=True, exist_ok=True)
    for pin in json.loads(PINS.read_text()):
        if pin["id"] not in selected:
            continue
        kind = pin.get("kind", "tar")
        extension = {"tar": ".tar.gz", "zip": ".zip", "docker": ".tar"}[kind]
        archive = root / (pin["id"] + extension)
        if not archive.exists():
            temporary = archive.with_suffix(archive.suffix + ".part")
            print(f"Downloading {pin['id']} from {pin['url']}", flush=True)
            with urllib.request.urlopen(pin["url"], timeout=120) as response, temporary.open("wb") as out:
                shutil.copyfileobj(response, out)
            if file_hash(temporary) != pin["archive_sha256"]:
                raise ValueError(f"Archive checksum mismatch: {temporary}")
            temporary.replace(archive)
        if file_hash(archive) != pin["archive_sha256"]:
            raise ValueError(f"Archive checksum mismatch: {archive}")
        extract_archive(archive, root / pin["id"], kind)


def generate(sources, output, selected):
    corpus = Corpus(sources, output)
    manifest = output / "paper-manifest.json"
    previous = json.loads(manifest.read_text()) if manifest.exists() else []
    for suite, generator in GENERATORS.items():
        if suite in selected:
            print(f"Translating {suite}", flush=True)
            generator(corpus)
    ml_suites(corpus, selected)
    new_paths = {row["path"] for row in corpus.entries}
    for row in previous:
        if row["suite"].split("/")[0] not in selected:
            corpus.entries.append(row)
        elif row["path"] not in new_paths:
            (output / safe_relative(row["path"])).unlink(missing_ok=True)
    corpus.entries.sort(key=lambda row: row["path"])
    corpus.save()
    print(f"{len(corpus.entries)} benchmark programs in {manifest}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", type=Path, required=True, help="Directory containing the pinned upstream sources")
    parser.add_argument("--output", type=Path, default=ROOT / "examples/benchmarks")
    parser.add_argument(
        "--suite",
        action="append",
        choices=sorted(set(GENERATORS) | ML_SUITES),
        help="Repeat to select suites; defaults to all",
    )
    parser.add_argument(
        "--fetch",
        action="store_true",
        help="Download/check pinned archives and extract source files first (SynMem: 2.9 GB, ASAC: 527 MB)",
    )
    args = parser.parse_args()
    selected = set(args.suite or (set(GENERATORS) | ML_SUITES))
    if args.fetch:
        fetch_sources(args.sources, selected)
    generate(args.sources, args.output, selected)


if __name__ == "__main__":
    main()
