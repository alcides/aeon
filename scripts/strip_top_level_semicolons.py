#!/usr/bin/env python3
"""Remove optional top-level statement semicolons from .ae files (Lean-style).

Only strips lines at brace depth 0 so block internals like ``x: Int = 1;`` keep
their semicolons (grammar still requires ``;`` or ``in`` there).
"""

from __future__ import annotations

import sys
from pathlib import Path


def _strip_strings_for_brace_scan(s: str) -> str:
    out: list[str] = []
    i = 0
    while i < len(s):
        if s[i] == '"':
            out.append(" ")
            i += 1
            while i < len(s):
                if s[i] == "\\":
                    i += 2
                    continue
                if s[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        if s[i] == "#":
            break
        out.append(s[i])
        i += 1
    return "".join(out)


def _brace_delta(line: str) -> int:
    t = _strip_strings_for_brace_scan(line)
    return t.count("{") - t.count("}")


def _def_line_needs_trailing_semicolon(body: str) -> bool:
    """If True, a trailing ``;`` on this ``def`` line is grammar-required (do not strip)."""
    s = body.strip()
    if not s.startswith("def"):
        return False
    if "=" not in s:
        return False
    i = s.index("=")
    return "=" in s[i + 1 :]


def _ends_statement_semicolon(line: str) -> bool:
    body = line.rstrip("\r\n")
    if not body.rstrip().endswith(";"):
        return False
    core = body.rstrip()[:-1].rstrip()
    in_str = False
    esc = False
    for c in core:
        if esc:
            esc = False
            continue
        if c == "\\":
            esc = True
            continue
        if c == '"':
            in_str = not in_str
    return not in_str


def process_text(text: str) -> str:
    depth = 0
    out_lines: list[str] = []
    for line in text.splitlines(keepends=True):
        if line.endswith("\r\n"):
            eol, body = "\r\n", line[:-2]
        elif line.endswith("\n"):
            eol, body = "\n", line[:-1]
        elif line.endswith("\r"):
            eol, body = "\r", line[:-1]
        else:
            eol, body = "", line

        # Only strip statement-ending ";" on true top-level lines. Indented
        # lines (e.g. ``a = e;`` inside ``def f =`` bodies) need ";" for the
        # let/rec grammar (``("in"|";") expression``).
        if (
            depth == 0
            and body == body.lstrip()
            and _ends_statement_semicolon(body)
            and not _def_line_needs_trailing_semicolon(body)
        ):
            body = body.rstrip()[:-1].rstrip()

        out_lines.append(body + eol)
        depth += _brace_delta(body)
        depth = max(0, depth)

    return "".join(out_lines)


def main(argv: list[str]) -> int:
    roots = [Path(p) for p in (argv[1:] or ["examples", "libraries"])]
    for root in roots:
        if not root.exists():
            print(f"skip missing {root}", file=sys.stderr)
            continue
        for path in sorted(root.rglob("*.ae")):
            raw = path.read_text(encoding="utf-8")
            new = process_text(raw)
            if new != raw:
                path.write_text(new, encoding="utf-8")
                print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
