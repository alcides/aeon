#!/usr/bin/env python3
"""Convert SyGuS PBE-Strings benchmarks (.sl) into aeon example-driven (PBE)
synthesis files (.ae) for the AFTA backend.

The BLAZE/SYNGAR paper (Wang, Dillig & Singh, POPL'18) evaluates its
abstraction-refinement FTA on the SyGuS string-transformation benchmark suite
(Alur et al. 2015). A benchmark is a ``synth-fun`` over a string DSL plus a set
of ``(constraint (= (f inputs...) output))`` input/output examples.

This script extracts the function signature and the I/O examples and emits:

    open String
    @example(f "in1" = "out1")
    ...
    def f (a0: String) (a1: Int) : String := (?hole : String);

which ``aeon --no-main --synthesizer afta`` solves by building a tree automaton
keyed on the example outputs.

Usage:
    python scripts/sygus_to_aeon.py SRC.sl                 # print to stdout
    python scripts/sygus_to_aeon.py SRC_DIR OUT_DIR        # batch a directory
"""

from __future__ import annotations

import sys
from pathlib import Path


# -- minimal s-expression reader ------------------------------------------


def tokenize(s: str) -> list[str]:
    out: list[str] = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c in "()":
            out.append(c)
            i += 1
        elif c == '"':
            j = i + 1
            buf = ['"']
            while j < n:
                if s[j] == '"':
                    # SMT-LIB escapes a quote by doubling it ("").
                    if j + 1 < n and s[j + 1] == '"':
                        buf.append('"')
                        j += 2
                        continue
                    buf.append('"')
                    j += 1
                    break
                buf.append(s[j])
                j += 1
            out.append("".join(buf))
            i = j
        elif c == ";":  # line comment
            while i < n and s[i] != "\n":
                i += 1
        elif c.isspace():
            i += 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in '()";':
                j += 1
            out.append(s[i:j])
            i = j
    return out


def parse(tokens: list[str], i: int = 0):
    """Parse one s-expression starting at index ``i``; return (node, next_i)."""
    tok = tokens[i]
    if tok == "(":
        lst = []
        i += 1
        while tokens[i] != ")":
            node, i = parse(tokens, i)
            lst.append(node)
        return lst, i + 1
    return tok, i + 1


def parse_all(s: str) -> list:
    tokens = tokenize(s)
    out = []
    i = 0
    while i < len(tokens):
        node, i = parse(tokens, i)
        out.append(node)
    return out


# -- SMT-LIB literal / type helpers ---------------------------------------

SMT_TO_AEON_TYPE = {"String": "String", "Int": "Int", "Bool": "Bool"}


def smt_type(t) -> str:
    if isinstance(t, str):
        return SMT_TO_AEON_TYPE.get(t, t)
    return "String"


def smt_literal_to_aeon(tok: str) -> str:
    """Render an SMT literal token as an aeon literal."""
    if tok.startswith('"') and tok.endswith('"'):
        inner = tok[1:-1]
        # aeon string literals: escape backslash and quote.
        inner = inner.replace("\\", "\\\\").replace('"', '\\"')
        return f'"{inner}"'
    if tok in ("true", "false"):
        return tok
    return tok  # integer literal


def is_call_to(node, fname: str) -> bool:
    return isinstance(node, list) and len(node) > 0 and node[0] == fname


# -- benchmark extraction --------------------------------------------------


# SMT-LIB string operators -> aeon String-library functions, for grammar
# scoping: each benchmark imports only the operators its SyGuS grammar allows,
# instead of all of ``open String`` -- a much smaller automaton alphabet.
SMT_OP_TO_AEON = {
    "str.++": "concat",
    "str.at": "charAt",
    "str.substr": "substr",
    "str.replace": "replace",
    "str.indexof": "indexOfFrom",
    "str.len": "len",
    "str.prefixof": "startsWith",
    "str.suffixof": "endsWith",
    "str.contains": "contains",
    "str.to.int": "stringToInt",
    "str.from_int": "intToString",
    "int.to.str": "intToString",
    "str.to_int": "stringToInt",
    "str.from-int": "intToString",
    "str.upper": "upper",
    "str.lower": "lower",
}


def _collect_symbols(node, acc: set[str]) -> None:
    if isinstance(node, list):
        for x in node:
            _collect_symbols(x, acc)
    elif isinstance(node, str):
        acc.add(node)


class Benchmark:
    def __init__(self, fname: str, args: list[tuple[str, str]], ret: str):
        self.fname = fname
        self.args = args  # [(name, aeon_type)]
        self.ret = ret  # aeon type
        self.examples: list[tuple[list[str], str]] = []  # ([arg literals], output literal)
        self.ops: list[str] = []  # aeon String funcs the grammar allows (scoping)


def extract(sl_text: str) -> Benchmark | None:
    forms = parse_all(sl_text)
    bench: Benchmark | None = None
    for form in forms:
        if not isinstance(form, list) or not form:
            continue
        head = form[0]
        if head == "synth-fun":
            fname = form[1]
            arglist = form[2]
            ret = smt_type(form[3])
            args = []
            for a in arglist:
                # (name Type)
                args.append((a[0], smt_type(a[1])))
            bench = Benchmark(fname, args, ret)
            # Grammar scoping: map the operators mentioned anywhere in the
            # synth-fun's grammar to aeon String functions (deduped, ordered).
            syms: set[str] = set()
            for extra in form[4:]:
                _collect_symbols(extra, syms)
            seen_ops: list[str] = []
            for smt_op, aeon_fn in SMT_OP_TO_AEON.items():
                if smt_op in syms and aeon_fn not in seen_ops:
                    seen_ops.append(aeon_fn)
            bench.ops = seen_ops
    if bench is None:
        return None
    for form in forms:
        if not (isinstance(form, list) and form and form[0] == "constraint"):
            continue
        body = form[1]
        # (= (f a0 a1 ...) out)  or  (= out (f ...))
        if not (isinstance(body, list) and len(body) == 3 and body[0] == "="):
            continue
        lhs, rhs = body[1], body[2]
        for call_side, out_side in ((lhs, rhs), (rhs, lhs)):
            if is_call_to(call_side, bench.fname) and isinstance(out_side, str):
                inputs = [smt_literal_to_aeon(a) for a in call_side[1:]]
                output = smt_literal_to_aeon(out_side)
                bench.examples.append((inputs, output))
                break
    return bench if bench.examples else None


def to_aeon(bench: Benchmark) -> str:
    # Scope to just the grammar's operators (smaller automaton alphabet). The
    # ``String`` type itself is a builtin, so a selective import suffices; fall
    # back to ``open String`` if the grammar mentioned no known operator.
    if bench.ops:
        header = f"import String ({', '.join(bench.ops)});"
    else:
        header = "open String"
    lines = [header, ""]
    lines.append("# Auto-generated from a SyGuS PBE-Strings benchmark (BLAZE/SYNGAR suite,")
    lines.append("# Wang, Dillig & Singh, POPL'18). Solve with:")
    lines.append("#   uv run python -m aeon --no-main -s afta examples/synthesis/afta/sygus/<file>.ae")
    lines.append("")
    for inputs, output in bench.examples:
        call = bench.fname + "".join(f" {a}" for a in inputs)
        lines.append(f"@example({call} = {output})")
    arg_decl = "".join(f" ({nm}: {ty})" for nm, ty in bench.args)
    lines.append(f"def {bench.fname}{arg_decl} : {bench.ret} := (?hole : {bench.ret});")
    return "\n".join(lines) + "\n"


def convert_file(src: Path) -> str | None:
    bench = extract(src.read_text())
    if bench is None:
        return None
    return to_aeon(bench)


def main(argv: list[str]) -> int:
    if len(argv) == 2:
        out = convert_file(Path(argv[1]))
        if out is None:
            print(f"# could not extract a PBE benchmark from {argv[1]}", file=sys.stderr)
            return 1
        sys.stdout.write(out)
        return 0
    if len(argv) == 3:
        src_dir, out_dir = Path(argv[1]), Path(argv[2])
        out_dir.mkdir(parents=True, exist_ok=True)
        ok = 0
        fail = 0
        for sl in sorted(src_dir.rglob("*.sl")):
            res = convert_file(sl)
            if res is None:
                fail += 1
                continue
            (out_dir / (sl.stem + ".ae")).write_text(res)
            ok += 1
        print(f"converted {ok} benchmark(s), skipped {fail}", file=sys.stderr)
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
