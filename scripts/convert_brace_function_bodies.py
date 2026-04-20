#!/usr/bin/env python3
"""Convert ``def f ... : T { body }`` to ``def f ... : T = body`` (Lean-style).

Preserves comments and formatting inside ``body``. Uses brace/string-aware scanning
so refinements ``{v:Int|...}`` in types and dict literals inside strings are not
confused with the function-body braces.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


def skip_ws(s: str, i: int) -> int:
    while i < len(s) and s[i] in " \t\n\r":
        i += 1
    return i


def _string_aware_scan(
    s: str,
    i: int,
    on_char,
) -> int:
    in_str = False
    esc = False
    while i < len(s):
        c = s[i]
        if in_str:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        i = on_char(s, i, c)
        if i < 0:
            return -i
        i += 1
    return i


def skip_balanced_parens(s: str, i: int) -> int:
    depth = 0

    def on_char(s2: str, j: int, c: str) -> int:
        nonlocal depth
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return -(j + 1)
        return j

    assert s[i] == "("
    return _string_aware_scan(s, i, on_char)


def skip_type_and_decreasing(s: str, i: int) -> int:
    """Return index at start of ``{`` (body), ``=`` (already eq-form), or error."""
    i = skip_ws(s, i)
    pdepth = 0
    bdepth = 0
    in_str = False
    esc = False
    while i < len(s):
        if pdepth == 0 and bdepth == 0 and not in_str:
            rest = s[i:].lstrip()
            ri = i + (len(s[i:]) - len(rest))
            if rest.startswith("decreasing_by"):
                i = ri + len("decreasing_by")
                i = skip_ws(s, i)
                if i >= len(s) or s[i] != "[":
                    return i
                b = 0
                in2 = False
                esc2 = False
                while i < len(s):
                    c = s[i]
                    if in2:
                        if esc2:
                            esc2 = False
                        elif c == "\\":
                            esc2 = True
                        elif c == '"':
                            in2 = False
                        i += 1
                        continue
                    if c == '"':
                        in2 = True
                        i += 1
                        continue
                    if c == "[":
                        b += 1
                    elif c == "]":
                        b -= 1
                        if b == 0:
                            i += 1
                            break
                    i += 1
                i = skip_ws(s, i)
                continue
            if rest.startswith("=") or rest.startswith("{"):
                return ri
        c = s[i]
        if in_str:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if c == "(":
            pdepth += 1
        elif c == ")":
            pdepth -= 1
        elif c == "{":
            bdepth += 1
        elif c == "}":
            bdepth -= 1
        i += 1
    return len(s)


def extract_braced_body(s: str, open_brace: int) -> tuple[str, int]:
    depth = 0
    in_str = False
    esc = False
    i = open_brace
    start_content = open_brace + 1
    while i < len(s):
        c = s[i]
        if in_str:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return s[start_content:i], i + 1
        i += 1
    raise ValueError(f"unclosed '{{' starting near {open_brace}")


def _in_string_before(s: str, idx: int) -> bool:
    in_str = False
    esc = False
    i = 0
    while i < idx:
        c = s[i]
        if in_str:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
        i += 1
    return in_str


def find_soft_def_starts(s: str) -> list[int]:
    out: list[int] = []
    for m in re.finditer(r"(?m)\bdef\s+", s):
        idx = m.start()
        if _in_string_before(s, idx):
            continue
        line_start = s.rfind("\n", 0, idx) + 1
        if "#" in s[line_start:idx]:
            continue
        out.append(idx)
    return out


def maybe_convert_def_at(s: str, def_kw: int) -> tuple[int, int, str] | None:
    i = def_kw + len("def")
    i = skip_ws(s, i)
    if i >= len(s):
        return None
    while i < len(s) and (s[i].isalnum() or s[i] == "_" or s[i] == "?"):
        i += 1
    while True:
        i = skip_ws(s, i)
        if i < len(s) and s[i] == "(":
            i = skip_balanced_parens(s, i)
        else:
            break
    i = skip_ws(s, i)
    if i >= len(s) or s[i] != ":":
        return None
    i += 1
    j = skip_type_and_decreasing(s, i)
    j = skip_ws(s, j)
    if j >= len(s):
        return None
    if s[j] == "=":
        return None
    if s[j] != "{":
        return None
    inner, after = extract_braced_body(s, j)
    if inner.startswith("\n"):
        replacement = "=" + inner
    else:
        replacement = "= " + inner.strip()
    return (j, after, replacement)


def convert_file(text: str) -> tuple[str, int]:
    n = 0
    out: list[str] = []
    pos = 0
    for def_kw in find_soft_def_starts(text):
        if def_kw < pos:
            continue
        conv = maybe_convert_def_at(text, def_kw)
        if conv is None:
            continue
        brace_start, after_brace, replacement = conv
        out.append(text[pos:brace_start])
        out.append(replacement)
        pos = after_brace
        n += 1
    out.append(text[pos:])
    return "".join(out), n


def main(argv: list[str]) -> int:
    roots = [Path(p) for p in (argv[1:] or ["examples", "libraries"])]
    total = 0
    for root in roots:
        if not root.exists():
            print(f"skip missing {root}", file=sys.stderr)
            continue
        for path in sorted(root.rglob("*.ae")):
            raw = path.read_text(encoding="utf-8")
            new, k = convert_file(raw)
            if k:
                path.write_text(new, encoding="utf-8")
                print(f"{path} ({k})")
                total += k
    print(f"total conversions: {total}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
