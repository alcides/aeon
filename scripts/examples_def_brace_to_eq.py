#!/usr/bin/env python3
"""Convert ``def f : T { e }`` to ``def f : T = e;`` in Aeon example files.

Conservative about comments and strings; uses a small type parser so return-type
refinements like ``{x:Int|...}`` are not mistaken for the function body ``{``.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


def _skip_string(src: str, i: int, n: int) -> int:
    quote = src[i]
    j = i + 1
    while j < n:
        ch = src[j]
        if ch == "\\":
            j += 2
            continue
        if ch == quote:
            return j + 1
        j += 1
    return n


def _skip_ws(src: str, i: int, n: int) -> int:
    while i < n and src[i].isspace():
        i += 1
    return i


def _parse_type(src: str, i: int, n: int) -> int:
    i = _skip_ws(src, i, n)

    def parse_atom(j: int) -> int:
        j = _skip_ws(src, j, n)
        if j >= n:
            return j
        if src.startswith("forall", j) and (j + 6 >= n or not (src[j + 6].isalnum() or src[j + 6] == "_")):
            j += len("forall")
            j = _skip_ws(src, j, n)
            if j < n and src[j] == "<":
                depth = 1
                j += 1
                while j < n and depth:
                    ch = src[j]
                    if ch == "#":
                        while j < n and src[j] != "\n":
                            j += 1
                        continue
                    if ch in "\"'":
                        j = _skip_string(src, j, n)
                        continue
                    if j + 1 < n and ch == "-" and src[j + 1] == ">":
                        j += 2
                        continue
                    if ch == "<":
                        depth += 1
                    elif ch == ">":
                        depth -= 1
                    j += 1
            else:
                while j < n and (src[j].isalnum() or src[j] == "_"):
                    j += 1
                j = _skip_ws(src, j, n)
                if j < n and src[j] == ":":
                    j += 1
                    j = _skip_ws(src, j, n)
                    if j < n and src[j] in "B*":
                        j += 1
            j = _skip_ws(src, j, n)
            if j < n and src[j] == ",":
                j += 1
            j = _skip_ws(src, j, n)
            return parse_type_prime(j)
        if src[j] == "(":
            depth = 1
            j += 1
            while j < n and depth:
                ch = src[j]
                if ch == "#":
                    while j < n and src[j] != "\n":
                        j += 1
                    continue
                if ch in "\"'":
                    j = _skip_string(src, j, n)
                    continue
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                j += 1
            return j
        if src[j] == "{":
            depth = 1
            j += 1
            while j < n and depth:
                ch = src[j]
                if ch == "#":
                    while j < n and src[j] != "\n":
                        j += 1
                    continue
                if ch in "\"'":
                    j = _skip_string(src, j, n)
                    continue
                if j + 1 < n and ch == "-" and src[j + 1] == ">":
                    j += 2
                    continue
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
                j += 1
            return j
        while j < n and (src[j].isalnum() or src[j] in "_"):
            j += 1
        return j

    def parse_type_prime(j: int) -> int:
        j = parse_atom(j)
        j = _skip_ws(src, j, n)
        if j + 1 < n and src[j] == "-" and src[j + 1] == ">":
            return parse_type_prime(j + 2)
        return j

    return parse_type_prime(i)


def _skip_decreasing_by(src: str, i: int, n: int) -> int:
    i = _skip_ws(src, i, n)
    if not src.startswith("decreasing_by", i):
        return i
    j = i + len("decreasing_by")
    j = _skip_ws(src, j, n)
    if j >= n or src[j] != "[":
        return j
    depth = 1
    j += 1
    while j < n and depth:
        ch = src[j]
        if ch == "#":
            while j < n and src[j] != "\n":
                j += 1
            continue
        if ch in "\"'":
            j = _skip_string(src, j, n)
            continue
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        j += 1
    return j


def _match_brace_body(src: str, body_open: int, n: int) -> int:
    assert body_open < n and src[body_open] == "{"
    t = body_open + 1
    depth = 1
    while t < n and depth:
        ch = src[t]
        if ch == "#":
            while t < n and src[t] != "\n":
                t += 1
            continue
        if ch in "\"'":
            t = _skip_string(src, t, n)
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        t += 1
    return t


def convert_defs_brace_to_eq(src: str) -> tuple[str, bool]:
    out: list[str] = []
    i = 0
    changed = False
    n = len(src)

    while i < n:
        m_start = src.find("def ", i)
        if m_start == -1:
            out.append(src[i:])
            break

        line_start = src.rfind("\n", 0, m_start) + 1
        ls = line_start
        while ls < n and src[ls].isspace():
            ls += 1
        if ls < n and src[ls] == "#":
            line_end = src.find("\n", m_start)
            if line_end == -1:
                line_end = n
            else:
                line_end += 1
            out.append(src[i:line_end])
            i = line_end
            continue

        if m_start > 0 and src[m_start - 1] not in "\n\r\t ":
            out.append(src[i : m_start + 1])
            i = m_start + 1
            continue

        out.append(src[i:m_start])
        i = m_start
        j = i + 4

        while j < n and src[j].isspace():
            j += 1
        while j < n and (src[j].isalnum() or src[j] in "_"):
            j += 1

        while j < n:
            while j < n and src[j].isspace():
                j += 1
            if j < n and src[j] == "(":
                depth = 1
                j += 1
                while j < n and depth:
                    c = src[j]
                    if c == "#":
                        while j < n and src[j] != "\n":
                            j += 1
                        continue
                    if c in "\"'":
                        j = _skip_string(src, j, n)
                        continue
                    if c == "(":
                        depth += 1
                    elif c == ")":
                        depth -= 1
                    j += 1
                continue
            break

        j = _skip_ws(src, j, n)
        if j >= n or src[j] != ":":
            out.append(src[i:j])
            i = j
            continue

        j += 1
        type_end = _parse_type(src, j, n)
        k = _skip_decreasing_by(src, type_end, n)
        k = _skip_ws(src, k, n)
        if k < n and src[k] == "=":
            out.append(src[i:k])
            t = k + 1
            p2 = b2 = 0
            while t < n:
                ch = src[t]
                if ch == "#":
                    while t < n and src[t] != "\n":
                        t += 1
                    continue
                if ch in "\"'":
                    t = _skip_string(src, t, n)
                    continue
                if ch == "(":
                    p2 += 1
                elif ch == ")":
                    p2 -= 1
                elif ch == "{":
                    b2 += 1
                elif ch == "}":
                    b2 -= 1
                if ch == ";" and p2 == 0 and b2 == 0:
                    t += 1
                    break
                t += 1
            out.append(src[k:t])
            i = t
            continue

        if k < n and src[k] == "{":
            body_open = k
            body_close_end = _match_brace_body(src, body_open, n)
            body_close = body_close_end - 1
            body = src[body_open + 1 : body_close]
            prefix = src[i:body_open]
            new_body = body.strip()
            if not new_body.endswith(";"):
                new_body += ";"
            # Do not append ``src[body_close_end:]`` here: ``i`` will advance to
            # ``body_close_end`` and the main loop will copy the tail exactly once.
            out.append(prefix + "= " + new_body)
            changed = True
            i = body_close_end
            continue

        rel = re.search(r"\n\s*def\s+", src[m_start + 1 :])
        if not rel:
            out.append(src[m_start:])
            break
        split = m_start + 1 + rel.start()
        out.append(src[m_start:split])
        i = split

    return "".join(out), changed


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("roots", nargs="+", type=Path, help="Directories or files to rewrite")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--no-verify", action="store_true")
    args = ap.parse_args()

    def verify(path: Path) -> bool:
        if args.no_verify:
            return True
        try:
            from aeon.sugar.bind import bind_program
            from aeon.sugar.parser import parse_main_program

            txt = path.read_text(encoding="utf-8")
            prog = parse_main_program(txt, filename=str(path))
            bind_program(prog, [])
        except Exception:
            return False
        return True

    paths: list[Path] = []
    for root in args.roots:
        if root.is_file():
            paths.append(root)
        else:
            paths.extend(sorted(root.rglob("*.ae")))

    failed: list[Path] = []
    for path in paths:
        src = path.read_text(encoding="utf-8")
        new, changed = convert_defs_brace_to_eq(src)
        if not changed:
            if args.check:
                print(f"{path}: unchanged")
            continue
        if args.check:
            print(f"{path}: would_change")
            continue
        path.write_text(new, encoding="utf-8")
        if not verify(path):
            path.write_text(src, encoding="utf-8")
            print(f"reverted (aeon failed): {path}", file=sys.stderr)
            failed.append(path)
        else:
            print(f"updated: {path}")

    if failed:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
