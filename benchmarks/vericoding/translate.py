#!/usr/bin/env python3
"""Dafny -> Aeon translator for the Vericoding benchmark.

V1 subset (intentionally narrow):
  * Preamble contains only `predicate` definitions; no Dafny `function`.
  * Method args and return are `int` or `bool` only; single return value.
  * Predicate bodies are pure expressions over int/bool with the operators
    we know how to translate.
  * No quantifiers, no sequences/sets/maps/arrays/strings/chars/reals.

Tasks outside this subset are returned with a rejection reason; nothing is
emitted for them in v1.

Implication `a ==> b` is rewritten as aeon's `(a) --> (b)`.
Iff `a <==> b` is rewritten as `a = b` (valid for Bool operands).
Chained comparisons `a <= b <= c` are split into `(a <= b) && (b <= c)`.
"""

from __future__ import annotations

import re
from dataclasses import dataclass


@dataclass
class TaskSpec:
    id: str
    method_name: str
    args: list[tuple[str, str]]  # (name, dafny_type)
    return_name: str
    return_type: str  # int|bool
    requires: list[str]  # raw Dafny expression strings
    ensures: list[str]
    predicates: dict[str, "Predicate"]


@dataclass
class Predicate:
    name: str
    args: list[tuple[str, str]]
    body: str  # raw Dafny expression string


class TranslationError(Exception):
    """Raised when a Dafny task uses features outside the v1 subset."""


# ---- Dafny parsing -----------------------------------------------------------

BLOCKERS = re.compile(
    r"\b(seq<|set<|multiset<|multiset\b|map<|imap<|array<|array\b|array2<|"
    r"real\b|char\b|string\b|class\s+\w|trait\s+\w|datatype\s+\w|"
    r"ghost\s+(var|method|function)|lemma\s+\w|while\s*[\(\{]|"
    r"modifies\b|reads\b|decreases\b)"
)
# Dafny set-literal `{e1, e2, ...}` or membership `x in {...}` — separate
# pattern since `\{` isn't word-bounded.
SET_LITERAL = re.compile(r"\bin\s*\{|\{\s*\d+\s*,")
DAFNY_FUNCTION = re.compile(r"\bfunction\s+\w+\s*\(")
QUANT = re.compile(r"\b(forall|exists)\b\s+\w")

PREAMBLE_RE = re.compile(r"<vc-preamble>(.*?)</vc-preamble>", re.DOTALL)
SPEC_RE = re.compile(r"<vc-spec>(.*?)</vc-spec>", re.DOTALL)
METHOD_SIG = re.compile(
    r"method\s+(\w+)\s*\(([^)]*)\)\s*(?:returns\s*\(([^)]*)\))?",
    re.DOTALL,
)
PREDICATE_RE = re.compile(
    # Header: `predicate NAME(args)` then optionally one or more
    # `requires X` / `ensures X` clauses, then `{ body }`.
    # Body matched non-greedily on `}` since predicate bodies are not nested.
    r"predicate\s+(\w+)\s*\(([^)]*)\)\s*"
    r"(?:requires\s+[^\n]+\s*)*"
    r"(?:ensures\s+[^\n]+\s*)*"
    r"\{([^}]*)\}",
    re.DOTALL,
)
ARG_RE = re.compile(r"^\s*(\w+)\s*:\s*(int|bool)\s*$")


def _parse_args(s: str) -> list[tuple[str, str]]:
    s = s.strip()
    if not s:
        return []
    out: list[tuple[str, str]] = []
    for part in s.split(","):
        m = ARG_RE.match(part)
        if not m:
            raise TranslationError(f"unsupported arg/return type in {part!r}")
        out.append((m.group(1), m.group(2)))
    return out


_CLAUSE_ANCHOR = re.compile(
    r"\b(requires|ensures|decreases|modifies|reads)\b",
)


def _strip_dafny_comments(s: str) -> str:
    out = []
    i = 0
    in_line_comment = False
    in_block_comment = False
    while i < len(s):
        if in_line_comment:
            if s[i] == "\n":
                in_line_comment = False
                out.append("\n")
            i += 1
            continue
        if in_block_comment:
            if s[i : i + 2] == "*/":
                in_block_comment = False
                i += 2
                continue
            i += 1
            continue
        if s[i : i + 2] == "//":
            in_line_comment = True
            i += 2
            continue
        if s[i : i + 2] == "/*":
            in_block_comment = True
            i += 2
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def _extract_clauses(spec_body: str) -> tuple[list[str], list[str]]:
    """Pull `requires X` and `ensures X` clauses from a spec body.

    Each clause's RHS extends from the keyword to the next `requires`/`ensures`/
    `decreases`/`modifies`/`reads` keyword, or to the end of the spec body —
    so multi-line ensures clauses are captured whole. Comments are stripped
    first so they don't truncate or pollute clause bodies.
    """
    clean = _strip_dafny_comments(spec_body)
    # Find each clause-start position.
    matches = list(_CLAUSE_ANCHOR.finditer(clean))
    requires: list[str] = []
    ensures: list[str] = []
    for k, m in enumerate(matches):
        kw = m.group(1)
        start = m.end()
        end = matches[k + 1].start() if k + 1 < len(matches) else len(clean)
        body = clean[start:end].strip().rstrip(";").strip()
        if not body:
            continue
        if kw == "requires":
            requires.append(body)
        elif kw == "ensures":
            ensures.append(body)
        # Other anchors (`decreases`/`modifies`/`reads`) are filtered out by
        # BLOCKERS at the top level for v1; we ignore here.
    return requires, ensures


def parse_dafny(text: str, task_id: str) -> TaskSpec:
    if BLOCKERS.search(text):
        raise TranslationError("uses blocker feature (seq/set/map/array/string/class/lemma/etc.)")
    if SET_LITERAL.search(text):
        raise TranslationError("uses set literal / `in {...}` membership")
    if QUANT.search(text):
        raise TranslationError("uses quantifier (forall/exists)")

    m_pre = PREAMBLE_RE.search(text)
    m_spec = SPEC_RE.search(text)
    if not m_spec:
        raise TranslationError("missing <vc-spec> block")
    pre_body = m_pre.group(1) if m_pre else ""
    spec_body = m_spec.group(1)

    if DAFNY_FUNCTION.search(pre_body):
        raise TranslationError("preamble contains Dafny `function` (v1 supports only `predicate`)")

    predicates: dict[str, Predicate] = {}
    for m in PREDICATE_RE.finditer(pre_body):
        pname = m.group(1)
        pargs = _parse_args(m.group(2))
        predicates[pname] = Predicate(pname, pargs, m.group(3).strip())

    m_m = METHOD_SIG.search(spec_body)
    if not m_m:
        raise TranslationError("no method signature in <vc-spec>")
    name, args_s, rets_s = m_m.group(1), m_m.group(2), m_m.group(3) or ""
    args = _parse_args(args_s)
    rets = _parse_args(rets_s)
    if len(rets) != 1:
        raise TranslationError(f"method must return exactly one value (got {len(rets)})")
    return_name, return_type = rets[0]

    requires, ensures = _extract_clauses(spec_body)

    spec = TaskSpec(
        id=task_id,
        method_name=name,
        args=args,
        return_name=return_name,
        return_type=return_type,
        requires=requires,
        ensures=ensures,
        predicates=predicates,
    )
    _validate_references(spec)
    return spec


_BOOL_KEYWORDS = {"true", "false", "if", "then", "else", "let", "in"}


def _validate_references(spec: TaskSpec) -> None:
    """Reject tasks that call functions not defined by the preamble or our
    built-in shims. Keeps emit clean — the alternative is silent aeon errors.
    """
    defined = set(spec.predicates) | set(DAFNY_BUILTINS_AEON)
    call_re = re.compile(r"\b([A-Za-z_]\w*)\s*\(")
    texts = list(spec.requires) + list(spec.ensures) + [p.body for p in spec.predicates.values()]
    seen_unknown: set[str] = set()
    for t in texts:
        for m in call_re.finditer(t):
            name = m.group(1)
            if name in defined or name in _BOOL_KEYWORDS:
                continue
            seen_unknown.add(name)
    if seen_unknown:
        raise TranslationError(f"undefined symbols referenced: {sorted(seen_unknown)}")


# ---- Dafny expression -> Aeon expression -------------------------------------
#
# We do a token-level rewrite. The Dafny expressions in our subset are
# arithmetic/boolean trees over identifiers; we don't need a full parser.
# Steps, in order, on a string:
#   1. Strip trailing `;` and surrounding whitespace.
#   2. Rewrite `<==>` -> `==` (Bool iff).
#   3. Rewrite `==>` -> aeon's `-->` (right-associative).
#   4. Expand chained comparisons `a OP b OP c` -> `(a OP b) && (b OP c)`.
#   5. Pass through everything else.
#
# Implication expansion is the tricky bit: we need to know the bracketing of
# the LHS and RHS of `==>`. We parse parens to find the smallest enclosing
# operand on each side.

CMP_OPS = ("<=", ">=", "<", ">")
DAFNY_TYPE_TO_AEON = {"int": "Int", "bool": "Bool"}


def _strip(s: str) -> str:
    return s.strip().rstrip(";").strip()


def _split_balanced(s: str, sep: str) -> list[str]:
    """Split `s` on top-level (depth-0) occurrences of `sep`."""
    out, depth, buf = [], 0, []
    i = 0
    while i < len(s):
        c = s[i]
        if c == "(":
            depth += 1
            buf.append(c)
        elif c == ")":
            depth -= 1
            buf.append(c)
        elif depth == 0 and s[i : i + len(sep)] == sep:
            out.append("".join(buf))
            buf = []
            i += len(sep)
            continue
        else:
            buf.append(c)
        i += 1
    out.append("".join(buf))
    return out


def _recurse_into_parens(s: str, fn) -> str:
    """Apply `fn` to each top-level parenthesized subexpression in `s`."""
    out = []
    i = 0
    while i < len(s):
        if s[i] == "(":
            depth = 0
            j = i
            while j < len(s):
                if s[j] == "(":
                    depth += 1
                elif s[j] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= len(s):
                out.append(s[i:])
                break
            out.append("(" + fn(s[i + 1 : j]) + ")")
            i = j + 1
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def _expand_implication(s: str) -> str:
    """Rewrite Dafny `==>` into aeon's `-->`, at every depth.

    Implication is right-assoc in Dafny: `a ==> b ==> c` == `a ==> (b ==> c)`,
    and aeon's `-->` is right-assoc too, so we keep that grouping. `-->` is now
    registered in aeon's prelude, so no desugaring to `(!(a)) || (b)` is needed.
    """
    # First recurse into parens.
    s = _recurse_into_parens(s, _expand_implication)
    parts = _split_balanced(s, "==>")
    if len(parts) == 1:
        return s
    parts = [p.strip() for p in parts]
    out = f"({parts[-1]})"
    for p in reversed(parts[:-1]):
        out = f"(({p}) --> {out})"
    return out


def _expand_iff(s: str) -> str:
    """Rewrite `<==>` (left-assoc) as `==`, at every depth."""
    s = _recurse_into_parens(s, _expand_iff)
    parts = _split_balanced(s, "<==>")
    if len(parts) == 1:
        return s
    return " == ".join(f"({p.strip()})" for p in parts)


def _find_top_ops(text: str, ops: tuple[str, ...]) -> list[tuple[int, str]]:
    """Return positions of top-level (depth-0) occurrences of any op in `ops`.

    Longest-first match. `<` excluded when followed by `=`; `>` likewise.
    `=` excluded when part of `==`/`!=`/`<=`/`>=`.
    """
    spans: list[tuple[int, str]] = []
    depth = 0
    i = 0
    longest_first = sorted(ops, key=len, reverse=True)
    while i < len(text):
        c = text[i]
        if c == "(":
            depth += 1
            i += 1
            continue
        if c == ")":
            depth -= 1
            i += 1
            continue
        if depth == 0:
            matched = False
            for op in longest_first:
                if text[i : i + len(op)] == op:
                    if op == "<" and text[i : i + 2] == "<=":
                        continue
                    if op == ">" and text[i : i + 2] == ">=":
                        continue
                    # The `>` tail of an implication `-->` is not a comparison.
                    if op == ">" and i >= 2 and text[i - 2 : i + 1] == "-->":
                        continue
                    spans.append((i, op))
                    i += len(op)
                    matched = True
                    break
            if matched:
                continue
        i += 1
    return spans


def _expand_chained_comparison_pure(s: str) -> str:
    """Rewrite `a <= b <= c` into `(a <= b) && (b <= c)`.

    Caller must guarantee `s` does not contain top-level `&&`, `||`, `==>`, `<==>`
    so that every top-level comparison op participates in a single chain.
    """
    ops = _find_top_ops(s, CMP_OPS)
    if len(ops) < 2:
        return s
    parts: list[str] = []
    last = 0
    op_seq: list[str] = []
    for i, op in ops:
        parts.append(s[last:i])
        op_seq.append(op)
        last = i + len(op)
    parts.append(s[last:])
    parts = [p.strip() for p in parts]
    pieces = [f"({lhs} {op} {rhs})" for op, lhs, rhs in zip(op_seq, parts[:-1], parts[1:])]
    return " && ".join(pieces)


def _expand_chained_comparison(s: str) -> str:
    """Recursively expand chained comparisons at every nesting depth.

    Strategy: first descend into every top-level `(...)` subexpression and
    recurse, then split on top-level `&&` / `||` (logical separators) and
    recurse into each conjunct, then apply the pure chain expander to atomic
    comparison-only chunks.
    """
    # 1. Recurse into top-level parenthesized subexpressions.
    rebuilt = []
    i = 0
    while i < len(s):
        if s[i] == "(":
            # Find matching close paren.
            depth = 0
            j = i
            while j < len(s):
                if s[j] == "(":
                    depth += 1
                elif s[j] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= len(s):
                rebuilt.append(s[i:])
                break
            inner = s[i + 1 : j]
            rebuilt.append("(" + _expand_chained_comparison(inner) + ")")
            i = j + 1
        else:
            rebuilt.append(s[i])
            i += 1
    s2 = "".join(rebuilt)

    # 2. Split on top-level `&&` / `||` and recurse into each piece. Each piece
    #    is wrapped in parens because aeon's grammar makes `==`/`!=`/`&&`/`||`
    #    all right-associative at the same precedence; without parens
    #    `a == 1 && b == 2` parses as `a == (1 && (b == 2))` (a type error).
    spans = _find_top_ops(s2, ("&&", "||"))
    if spans:
        parts: list[str] = []
        op_seq: list[str] = []
        last = 0
        for k, op in spans:
            parts.append(s2[last:k])
            op_seq.append(op)
            last = k + len(op)
        parts.append(s2[last:])
        expanded = [_expand_chained_comparison_pure(p.strip()) for p in parts]
        wrapped = [_paren_unless_atomic(p) for p in expanded]
        out = wrapped[0]
        for op, rhs in zip(op_seq, wrapped[1:]):
            out = f"{out} {op} {rhs}"
        return out

    # 3. No logical operators at this depth: this is a comparison-only chunk.
    return _expand_chained_comparison_pure(s2)


CALL_RE = re.compile(r"\b([A-Za-z_]\w*)\s*\(")
_NOT_A_CALL = {
    # Aeon keywords / built-ins that may precede `(` for grouping, not call.
    "in",
    "let",
    "if",
    "then",
    "else",
    "match",
    "with",
    "true",
    "false",
    "by",
    "def",
}


def _rewrite_calls(s: str) -> str:
    """Rewrite Dafny call syntax `f(a, b, c)` into aeon curried form `(f a b c)`.

    Skips Aeon keywords (`in`, `let`, `if`, ...) — `in (X)` is a let-binding
    separator followed by a parenthesized expression, not a call.
    """
    out = []
    i = 0
    while i < len(s):
        m = CALL_RE.match(s, i)
        if not m:
            out.append(s[i])
            i += 1
            continue
        name = m.group(1)
        if name in _NOT_A_CALL:
            # Treat as a regular identifier; let the next iteration handle the `(`.
            out.append(name)
            i = m.end() - 1  # back up to the `(` so it's processed normally
            continue
        # Find the matching close paren.
        depth = 0
        j = m.end() - 1  # at '('
        start_args = m.end()
        while j < len(s):
            if s[j] == "(":
                depth += 1
            elif s[j] == ")":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if j >= len(s):
            # Unbalanced — fall back.
            out.append(s[i])
            i += 1
            continue
        inner = s[start_args:j]
        args = [a.strip() for a in _split_balanced(inner, ",")] if inner.strip() else []
        # Recursively rewrite each arg.
        args = [_rewrite_calls(a) for a in args]
        if not args:
            # Treat `f()` as `(f Unit)` — not encountered in v1 subset, conservative.
            out.append(f"({name})")
        else:
            out.append("(" + " ".join([name, *(_paren_if_needed(a) for a in args)]) + ")")
        i = j + 1
    return "".join(out)


def _paren_unless_atomic(s: str) -> str:
    """Wrap `s` in parens unless it's already a parenthesized expression or a
    single atom (identifier or literal). Used at conjunct/disjunct boundaries
    in `_expand_chained_comparison` so that aeon's right-assoc `==`/`&&`/`||`
    don't reassociate across boundaries.
    """
    s = s.strip()
    if not s:
        return s
    if re.fullmatch(r"-?\w+", s) or re.fullmatch(r"true|false", s):
        return s
    if s.startswith("(") and s.endswith(")"):
        depth = 0
        balanced_at_end = False
        for k, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    balanced_at_end = k == len(s) - 1
                    break
        if balanced_at_end:
            return s
    return f"({s})"


def _paren_if_needed(s: str) -> str:
    """Wrap argument in parens if it contains top-level operators or whitespace."""
    s = s.strip()
    if not s:
        return s
    # Already paren-wrapped: leave alone.
    if s.startswith("(") and s.endswith(")"):
        depth = 0
        balanced_at_start = False
        for k, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    balanced_at_start = k == len(s) - 1
                    break
        if balanced_at_start:
            return s
    # Single identifier / literal: no parens needed.
    if re.fullmatch(r"-?\w+", s):
        return s
    return f"({s})"


_VAR_DECL_LEAD = re.compile(r"\bvar\s+(\w+)\s*:=\s*([^;]+);\s*")

# Unary minus on an integer literal OR a simple identifier in a position where
# aeon's grammar expects `expression_bool` (which doesn't allow leading `-`):
# right after `(`, `,`, any binary operator, or start of expression.
# Replace `-X` -> `(0 - X)`.
_NEG_RE = re.compile(r"(^|[\(\[,]|==|!=|<=|>=|<|>|&&|\|\||\+|\-|\*|/|%|=)\s*-(\w+)")


def _wrap_negative_literals(s: str) -> str:
    prev = None
    cur = s
    # Apply repeatedly: a single pass may not match adjacent negatives.
    while prev != cur:
        prev = cur
        cur = _NEG_RE.sub(lambda m: f"{m.group(1)} (0 - {m.group(2)})", cur)
    return cur


def _expand_var_bindings(s: str) -> str:
    """Rewrite a leading sequence of `var X := EXPR;` (Dafny `function`/`predicate`
    let-bindings) into aeon `let X = EXPR in (REST)`, with explicit parens
    around REST so subsequent chain/`&&` rewrites don't escape the let scope.
    """
    bindings: list[tuple[str, str]] = []
    while True:
        m = _VAR_DECL_LEAD.match(s)
        if not m:
            break
        name, rhs = m.group(1), m.group(2).strip()
        bindings.append((name, rhs))
        s = s[m.end() :]
    if not bindings:
        return s
    body = s.strip()
    out = f"({body})"
    for name, rhs in reversed(bindings):
        out = f"let {name} := {rhs} in {out}"
    return out


def translate_expression(expr: str) -> str:
    """Translate a single Dafny expression (Boolean or arithmetic) to Aeon.

    Order matters:
      * `var X := Y;` let-bindings come out first so subsequent rewrites
        see plain expressions.
      * `<==>` and `==>` must be consumed before chain expansion, so the chain
        expander doesn't see the `>` in `==>` as a comparison op.
      * Chain expansion descends into parens, so the parens introduced by
        implication-rewriting don't hide nested chains.
    """
    s = _strip(expr)
    s = _expand_var_bindings(s)
    s = _expand_iff(s)
    s = _expand_implication(s)
    s = _expand_chained_comparison(s)
    s = _rewrite_calls(s)
    s = _wrap_negative_literals(s)
    # Aeon now follows Lean: equality is written `=` (was `==`). At this point all
    # `==>`/`<==>` have been consumed and let-bindings already emit `:=`, so every
    # remaining `==` is an equality operator.
    s = s.replace("==", "=")
    return s


# ---- Aeon emission -----------------------------------------------------------


def _aeon_args(args: list[tuple[str, str]]) -> str:
    return " ".join(f"({n}:{DAFNY_TYPE_TO_AEON[t]})" for n, t in args)


DAFNY_BUILTINS_AEON = {
    # Dafny's `abs` is a polymorphic absolute-value function; here we provide an
    # Int specialization sufficient for the v1 subset.
    "abs": "def abs (x:Int) : Int := if x >= 0 then x else 0 - x;",
}


def _needed_builtins(task: TaskSpec) -> list[str]:
    text = " ".join(task.requires + task.ensures + [p.body for p in task.predicates.values()])
    return [name for name in DAFNY_BUILTINS_AEON if re.search(rf"\b{name}\s*\(", text)]


def emit_aeon(task: TaskSpec) -> str:
    lines: list[str] = []
    lines.append(f"# Auto-translated from Vericoding {task.id}.")
    args_repr = ", ".join(f"{n}:{t}" for n, t in task.args)
    lines.append(
        f"# Original Dafny method: {task.method_name}({args_repr}) -> ({task.return_name}: {task.return_type})"
    )
    lines.append("")

    # Emit Dafny built-ins that this task references.
    for name in _needed_builtins(task):
        lines.append(DAFNY_BUILTINS_AEON[name])
    if _needed_builtins(task):
        lines.append("")

    # Emit predicates in their declaration order.
    for p in task.predicates.values():
        body = translate_expression(p.body)
        params = _aeon_args(p.args) or "(_unit:Int)"  # aeon requires >=1 arg
        if not p.args:
            # Predicate with no args: emit as a `def` constant of type Bool.
            lines.append(f"def {p.name} : Bool := {body};")
        else:
            lines.append(f"def {p.name} {params} : Bool := {body};")
    if task.predicates:
        lines.append("")

    # Build the precondition refinement (combined requires).
    pre_terms = [translate_expression(r) for r in task.requires]
    pre = " && ".join(f"({t})" for t in pre_terms) if pre_terms else None

    # Build the postcondition refinement (combined ensures).
    post_terms = [translate_expression(e) for e in task.ensures]
    if not post_terms:
        post = "true"
    else:
        post = " && ".join(f"({t})" for t in post_terms)

    aeon_args_list = list(task.args)
    if pre is not None and aeon_args_list:
        # Attach the precondition to the last arg as a refinement.
        last_name, last_type = aeon_args_list[-1]
        body_parts = []
        for n, t in aeon_args_list[:-1]:
            body_parts.append(f"({n}:{DAFNY_TYPE_TO_AEON[t]})")
        body_parts.append(f"({last_name}:{DAFNY_TYPE_TO_AEON[last_type]} | {pre})")
        args_str = " ".join(body_parts)
    elif aeon_args_list:
        args_str = _aeon_args(aeon_args_list)
    else:
        args_str = "(_unit:Int)"

    return_aeon = DAFNY_TYPE_TO_AEON[task.return_type]
    sig = f"def {task.method_name} {args_str} : {{{task.return_name}:{return_aeon} | {post}}} := ?hole;"
    lines.append(sig)
    return "\n".join(lines) + "\n"


# ---- Top-level entrypoint ----------------------------------------------------


def translate(text: str, task_id: str) -> str:
    spec = parse_dafny(text, task_id)
    return emit_aeon(spec)
