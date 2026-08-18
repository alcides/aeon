"""Typecheck a set of .ae files and report the failures.

Used while migrating the standard library to linear types: it gives a
per-file error count over the whole tree in one pass, which is a lot faster
than driving ``python -m aeon`` once per file.

    uv run python scripts/check_ae.py aeon/libraries examples
    uv run python scripts/check_ae.py --verbose aeon/libraries/Statistics.ae
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _config() -> AeonConfig:
    return AeonConfig(
        synthesizer="enumerative",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )


def check(path: Path) -> list[str]:
    try:
        return [str(e) for e in AeonDriver(_config()).parse(str(path))]
    except Exception as e:  # a crash is a failure like any other here
        return [f"{type(e).__name__}: {e}"]


def check_as_module(path: Path) -> list[str]:
    """Check a library the way it is actually used — through ``open``.

    A library's own members are unqualified inside its file, so method calls
    such as ``arr.length`` only resolve once the module is imported and its
    members are prefixed (``Array_length``)."""
    source = f'open {path.stem}\ndef main (args: Int) : Unit := print "ok";\n'
    try:
        return [str(e) for e in AeonDriver(_config()).parse(aeon_code=source)]
    except Exception as e:
        return [f"{type(e).__name__}: {e}"]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--verbose", "-v", action="store_true", help="print every error, not just the count")
    parser.add_argument("--limit", type=int, default=3, help="errors printed per file in verbose mode")
    parser.add_argument(
        "--as-module",
        action="store_true",
        help="check each file through `open <Name>` instead of directly (for aeon/libraries)",
    )
    args = parser.parse_args()

    files: list[Path] = []
    for raw in args.paths:
        p = Path(raw)
        files.extend(sorted(p.rglob("*.ae")) if p.is_dir() else [p])

    failed = 0
    for f in files:
        errors = check_as_module(f) if args.as_module else check(f)
        if not errors:
            continue
        failed += 1
        print(f"{f}: {len(errors)} error(s)")
        if args.verbose:
            for e in errors[: args.limit]:
                print(f"    {e[:300]}")
        sys.stdout.flush()

    print(f"\n{failed} of {len(files)} file(s) failed.")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
