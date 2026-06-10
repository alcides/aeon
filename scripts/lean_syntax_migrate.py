#!/usr/bin/env python3
"""Migrate Aeon surface syntax to the Lean-style convention.

Outside of string literals and ``#`` comments:

  * ``==`` (equality)        ->  ``=``
  * standalone ``=`` (def)   ->  ``:=``

Multi-character operators that merely *contain* ``=`` are preserved:
``<=``, ``>=``, ``!=``, ``=>`` (match/lambda arrow) and the already-Lean
``:=``. Python FFI code inside ``native "..."`` strings is left untouched so
that ``==`` in embedded Python keeps its meaning.

The transform is purely lexical and operates on a single character stream with
a tiny NORMAL / IN_STRING / IN_COMMENT state machine.
"""

from __future__ import annotations

import sys


def migrate(src: str) -> str:
    out: list[str] = []
    i = 0
    n = len(src)
    state = "NORMAL"
    while i < n:
        c = src[i]

        if state == "IN_STRING":
            out.append(c)
            if c == "\\" and i + 1 < n:  # escaped char: copy verbatim
                out.append(src[i + 1])
                i += 2
                continue
            if c == '"':
                state = "NORMAL"
            i += 1
            continue

        if state == "IN_COMMENT":
            out.append(c)
            if c == "\n":
                state = "NORMAL"
            i += 1
            continue

        # NORMAL
        if c == '"':
            state = "IN_STRING"
            out.append(c)
            i += 1
            continue
        if c == "#":
            state = "IN_COMMENT"
            out.append(c)
            i += 1
            continue

        if c == "=":
            prev = src[i - 1] if i > 0 else ""
            nxt = src[i + 1] if i + 1 < n else ""
            if nxt == "=":  # "==" equality -> "="
                out.append("=")
                i += 2
                continue
            if nxt == ">":  # "=>" arrow, keep
                out.append("=>")
                i += 2
                continue
            if prev in "<>!:":  # second char of <= >= != := , keep
                out.append("=")
                i += 1
                continue
            # standalone "=" definition -> ":="
            out.append(":=")
            i += 1
            continue

        out.append(c)
        i += 1

    return "".join(out)


def main(argv: list[str]) -> int:
    changed = 0
    for path in argv[1:]:
        with open(path, "r", encoding="utf-8") as f:
            src = f.read()
        new = migrate(src)
        if new != src:
            with open(path, "w", encoding="utf-8") as f:
                f.write(new)
            changed += 1
            print(f"migrated {path}")
    print(f"\n{changed} file(s) changed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
