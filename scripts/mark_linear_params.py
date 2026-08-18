"""Insert the ``1`` multiplicity on parameters whose type is a linear type.

Mechanical half of the linear-``Array`` migration: a parameter declared
``(xs: (Array Int))`` has to become ``(1 xs: (Array Int))`` now that
``Array`` is a ``linear type``. Bodies that use such a parameter more than
once need a ``copy`` and are left for a human to fix.

    uv run python scripts/mark_linear_params.py --dry-run aeon/libraries
    uv run python scripts/mark_linear_params.py examples/PSB2
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

# Types whose binders must carry multiplicity 1.
LINEAR = ("Array", "Dataset", "DataFrame", "Conn", "Txn", "StreamSocket", "DatagramSocket", "Rng")

_PARAM_START = re.compile(r"\(\s*(?P<name>[A-Za-z_][A-Za-z_0-9]*)\s*:")
_LINEAR_HEAD = re.compile(r"^\s*\(?\s*(?P<head>[A-Za-z_][A-Za-z_0-9]*)\b")
_REFINED_HEAD = re.compile(r"^\s*\{\s*[A-Za-z_][A-Za-z_0-9]*\s*:\s*\(?\s*(?P<head>[A-Za-z_][A-Za-z_0-9]*)\b")


def _matching_paren(text: str, open_idx: int) -> int | None:
    """Index of the ``)`` closing the ``(`` at ``open_idx``, or None."""
    depth = 0
    in_string = False
    i = open_idx
    while i < len(text):
        c = text[i]
        if in_string:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_string = False
        elif c == '"':
            in_string = True
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def _is_linear_type(type_text: str) -> bool:
    for pattern in (_REFINED_HEAD, _LINEAR_HEAD):
        m = pattern.match(type_text)
        if m:
            return m.group("head") in LINEAR
    return False


def transform(source: str) -> tuple[str, int]:
    out = source
    count = 0
    pos = 0
    while True:
        m = _PARAM_START.search(out, pos)
        if m is None:
            return out, count
        close = _matching_paren(out, m.start())
        if close is None:
            pos = m.end()
            continue
        type_text = out[m.end() : close]
        if _is_linear_type(type_text):
            insert_at = m.start() + 1
            # Keep the original spacing after ``(``.
            while out[insert_at] in " \t":
                insert_at += 1
            out = out[:insert_at] + "1 " + out[insert_at:]
            count += 1
            pos = insert_at + 2
        else:
            pos = m.end()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    files: list[Path] = []
    for raw in args.paths:
        p = Path(raw)
        files.extend(sorted(p.rglob("*.ae")) if p.is_dir() else [p])

    total = 0
    for f in files:
        source = f.read_text()
        new_source, n = transform(source)
        if n == 0:
            continue
        total += n
        print(f"{f}: {n} parameter(s)")
        if not args.dry_run:
            f.write_text(new_source)
    print(f"\n{total} parameter(s) in {len(files)} file(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
