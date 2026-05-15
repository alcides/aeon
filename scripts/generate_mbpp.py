#!/usr/bin/env python3
"""Generate one self-contained Aeon synthesis benchmark per MBPP problem.

MBPP (Mostly Basic Programming Problems, Google Research) ships ~1000 short
Python problems, each with a prompt, a canonical solution and a handful of
``assert`` test cases. This script turns the sanitized subset into individual
``.ae`` files under ``examples/MBPP/``, one per problem.

Each generated file is fully self-contained:
  * the prompt is kept as a comment,
  * the problem's ``test_list`` assertions are embedded into a ``native``
    fitness function that returns the number of failing assertions as a Float,
  * a ``?hole`` of the inferred signature is the synthesis target, driven by
    ``@minimize_float``.

Python containers Aeon has no builtin for (tuples, dicts, sets) become
inductive datatypes. The shape of those datatypes is chosen per problem from
what its test literals look like:

  * **Uniform** tuples / sets are cons-lists whose element type is the actual
    Aeon primitive — e.g. ``inductive Tuple | tnil | tcons (hd:Int) (tl:Tuple)``.
  * **Record** tuples (mixed primitives in a fixed shape) get a single
    constructor with one argument per position — e.g. ``inductive Tuple |
    mk (a:String) (b:Int) (c:List) (d:Bool) : Tuple``.
  * **Nested** uniform tuples-of-tuples emit two inductive types
    (``InnerTuple`` + ``Tuple``).
  * **Polymorphic** is used only for the cases (just task 446 in the
    sanitized dataset) where the same function is exercised on tuples /
    lists of *different* element types across tests.

The embedded test data is emitted directly in the inductive runtime
representation so the assertions agree with what the synthesizer's
constructors produce.

Usage:
    python scripts/generate_mbpp.py [--source PATH_OR_URL] [--out DIR]

With no --source the sanitized dataset is fetched from the MBPP repository.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
import urllib.request
from collections.abc import Sequence
from pathlib import Path

SANITIZED_MBPP_URL = "https://raw.githubusercontent.com/google-research/google-research/master/mbpp/sanitized-mbpp.json"

# Aeon keywords / prelude names we must not collide with when naming arguments.
RESERVED = {
    "def",
    "type",
    "if",
    "then",
    "else",
    "let",
    "in",
    "native",
    "native_import",
    "uninterpreted",
    "forall",
    "inductive",
    "decreasing_by",
    "open",
    "import",
    "synth",
    "f",
    "main",
}

PRIMITIVES = {"Int", "Bool", "Float", "String"}

# task_id 446 is the one problem in the sanitized dataset whose tests apply
# the function to tuples / lists of *different* element types across runs.
POLYMORPHIC_TASKS = {446}


class CodeGenError(Exception):
    """Raised when a problem cannot be turned into a valid Aeon file."""


# ---------------------------------------------------------------------------
# Literal classification
# ---------------------------------------------------------------------------


def elt_kind(node: ast.AST) -> str:
    """Aeon-level kind of one Python literal."""
    try:
        value = ast.literal_eval(node)
    except (ValueError, TypeError, SyntaxError):
        return "Other"
    if isinstance(value, bool):
        return "Bool"
    if isinstance(value, int):
        return "Int"
    if isinstance(value, float):
        return "Float"
    if isinstance(value, str):
        return "String"
    if isinstance(value, list):
        return "List"
    if isinstance(value, tuple):
        return "Tuple"
    if isinstance(value, dict):
        return "Dict"
    if isinstance(value, set):
        return "Set"
    return "Other"


def classify_literal(node: ast.AST) -> str:
    """Aeon type name for one argument literal — primitive name or container."""
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        return classify_literal(node.operand)
    return elt_kind(node)


def _contains(node: ast.AST, target: ast.AST) -> bool:
    return any(n is target for n in ast.walk(node))


def find_call(test: ast.AST, names: set[str]) -> ast.Call | None:
    """Locate the call to one of the problem's functions inside an assert.

    MBPP canonical solutions often define helper functions before the entry
    point, so we match against every name defined in the snippet rather than
    assuming the first ``def``.
    """
    for n in ast.walk(test):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in names:
            return n
    return None


def find_expected(test: ast.AST, call: ast.Call) -> ast.AST | None:
    """Literal the call result is directly compared against, if any."""
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        left, right = test.left, test.comparators[0]
        if left is call:
            return right
        if right is call:
            return left
    return None


def infer_return_type(test: ast.AST, call: ast.Call) -> str:
    """Aeon kind for the function's return value, inferred from how it is used."""
    if test is call:
        return "Bool"
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return "Bool"
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        left, right = test.left, test.comparators[0]
        if _contains(left, call):
            wrapper, other = left, right
        elif _contains(right, call):
            wrapper, other = right, left
        else:
            return "Int"
        if wrapper is call:
            return classify_literal(other)
        if isinstance(wrapper, ast.Call) and isinstance(wrapper.func, ast.Name):
            wf = wrapper.func.id
            if wf in ("set", "sorted", "list", "len"):
                return "List"
            if wf == "str":
                return "String"
            if wf in ("int", "abs", "round", "sum", "min", "max"):
                return "Int"
            if wf == "float":
                return "Float"
            if wf == "tuple":
                return "Tuple"
            if wf == "dict":
                return "Dict"
        return classify_literal(other)
    if isinstance(test, ast.Call) and isinstance(test.func, ast.Attribute):
        if test.func.attr == "isclose":
            return "Float"
    return "Int"


def infer_arg_types(call: ast.Call) -> list[str]:
    return [classify_literal(arg) for arg in call.args]


# ---------------------------------------------------------------------------
# Strategy analysis
# ---------------------------------------------------------------------------
#
# Per container kind (tuple, dict, set) the generator picks the *narrowest*
# inductive shape that captures every literal of that kind in the problem's
# tests. The Strategy returned drives both the inductive declaration that goes
# at the top of the file and the runtime representation we embed in the
# fitness ``native`` string.


def _collect_literals(problem: dict, cls: type) -> list[ast.AST]:
    out: list[ast.AST] = []
    for src in problem["test_list"]:
        try:
            tree = ast.parse(src.strip())
        except SyntaxError:
            continue
        for node in ast.walk(tree):
            if isinstance(node, cls):
                out.append(node)
    return out


def _tuple_strategy(tuples: list[ast.Tuple]) -> dict | None:
    """Pick the strategy for representing every tuple literal in a problem."""
    if not tuples:
        return None

    shapes = [tuple(elt_kind(e) for e in t.elts) for t in tuples]

    # Nested-uniform: some literals are "outer" tuples whose elements are all
    # themselves tuples, the rest are uniform tuples of a single primitive, and
    # the two groups cover every literal in the problem.
    outer_shapes = [s for s in shapes if s and all(k == "Tuple" for k in s)]
    inner_uniform_shapes = [s for s in shapes if s and len(set(s)) == 1 and s[0] in PRIMITIVES]
    if outer_shapes and inner_uniform_shapes and len(outer_shapes) + len(inner_uniform_shapes) == len(shapes):
        inner_kinds = {s[0] for s in inner_uniform_shapes}
        if len(inner_kinds) == 1:
            return {"kind": "nested", "inner": next(iter(inner_kinds))}

    # Uniform: every literal is itself uniform (possibly empty) and all literals
    # share the same element kind.
    if all(len(set(s)) <= 1 for s in shapes):
        kinds = {s[0] for s in shapes if s}
        if len(kinds) <= 1:
            only = next(iter(kinds)) if kinds else "Int"
            if only in PRIMITIVES or only == "List":
                return {"kind": "uniform", "elt": only}

    # Record: every literal has the same fixed shape with primitive (or opaque
    # List) elements.
    if all(s == shapes[0] for s in shapes) and shapes[0]:
        if all(k in (PRIMITIVES | {"List"}) for k in shapes[0]):
            return {"kind": "record", "shape": shapes[0]}

    return None


def _dict_strategy(dicts: list[ast.Dict]) -> dict | None:
    """Pick a strategy for representing every dict literal in a problem."""
    if not dicts:
        return None
    key_kinds: set[str] = set()
    val_kinds: set[str] = set()
    for d in dicts:
        for k in d.keys:
            if k is not None:
                key_kinds.add(elt_kind(k))
        for v in d.values:
            val_kinds.add(elt_kind(v))
    if len(key_kinds) == 1 and len(val_kinds) == 1:
        key_kind, val_kind = next(iter(key_kinds)), next(iter(val_kinds))
        if key_kind in (PRIMITIVES | {"List", "Tuple"}) and val_kind in (PRIMITIVES | {"List", "Tuple"}):
            return {"kind": "uniform", "key": key_kind, "val": val_kind}
    return None


def _set_strategy(sets: list[ast.Set]) -> dict | None:
    if not sets:
        return None
    kinds: set[str] = set()
    for s in sets:
        for e in s.elts:
            kinds.add(elt_kind(e))
    if len(kinds) == 1 and next(iter(kinds)) in PRIMITIVES:
        return {"kind": "uniform", "elt": next(iter(kinds))}
    return None


def analyze_strategies(problem: dict) -> dict[str, dict | None]:
    """Compute the strategy dict for each container kind appearing in tests."""
    if problem["task_id"] in POLYMORPHIC_TASKS:
        return {
            "tuple": {"kind": "polymorphic"},
            "list": {"kind": "polymorphic"},
        }
    return {
        "tuple": _tuple_strategy([n for n in _collect_literals(problem, ast.Tuple) if isinstance(n, ast.Tuple)]),
        "dict": _dict_strategy([n for n in _collect_literals(problem, ast.Dict) if isinstance(n, ast.Dict)]),
        "set": _set_strategy([n for n in _collect_literals(problem, ast.Set) if isinstance(n, ast.Set)]),
    }


# ---------------------------------------------------------------------------
# Inductive declarations
# ---------------------------------------------------------------------------


def _uniform_decl(type_name: str, elt_aeon: str, cons_prefix: str) -> str:
    return (
        f"inductive {type_name}\n"
        f"| {cons_prefix}nil  : {type_name}\n"
        f"| {cons_prefix}cons (hd:{elt_aeon}) (tl:{type_name}) : {type_name}"
    )


def _record_decl(type_name: str, shape: tuple[str, ...]) -> str:
    args = " ".join(f"(a{i}:{kind})" for i, kind in enumerate(shape))
    return f"inductive {type_name}\n| mk {args} : {type_name}"


def _dict_uniform_decl(key_aeon: str, val_aeon: str) -> str:
    return f"inductive Dict\n| dnil : Dict\n| dcons (key:{key_aeon}) (val:{val_aeon}) (rest:Dict) : Dict"


def _polymorphic_decls() -> list[str]:
    return [
        "inductive Tuple a\n| tnil  : (Tuple a)\n| tcons (hd:a) (tl:(Tuple a)) : (Tuple a)",
        "inductive Seq a\n| snil  : (Seq a)\n| scons (hd:a) (tl:(Seq a)) : (Seq a)",
    ]


def declarations_for(strategies: dict[str, dict | None], list_decl_needed: bool) -> list[str]:
    """Emit every inductive declaration this file's strategies require."""
    decls: list[str] = []

    if any(s and s.get("kind") == "polymorphic" for s in strategies.values()):
        return _polymorphic_decls()

    if list_decl_needed:
        decls.append("type List")

    ts = strategies.get("tuple")
    if ts is not None:
        if ts["kind"] == "uniform":
            decls.append(_uniform_decl("Tuple", ts["elt"], "t"))
        elif ts["kind"] == "record":
            decls.append(_record_decl("Tuple", ts["shape"]))
        elif ts["kind"] == "nested":
            decls.append(_uniform_decl("InnerTuple", ts["inner"], "i"))
            decls.append(_uniform_decl("Tuple", "InnerTuple", "t"))
        elif ts["kind"] == "opaque":
            decls.append("type Tuple")

    ds = strategies.get("dict")
    if ds is not None:
        if ds["kind"] == "uniform":
            decls.append(_dict_uniform_decl(ds["key"], ds["val"]))
        elif ds["kind"] == "opaque":
            decls.append("type Dict")

    ss = strategies.get("set")
    if ss is not None:
        if ss["kind"] == "uniform":
            decls.append(_uniform_decl("Set", ss["elt"], "s"))
        elif ss["kind"] == "opaque":
            decls.append("type Set")

    return decls


# ---------------------------------------------------------------------------
# Test data conversion
# ---------------------------------------------------------------------------
#
# An Aeon inductive constructor ``C(a, b)`` evaluates to the tagged tuple
# ``('<TypeName>_<ConsName>', a, b)``. The conversion functions below emit the
# Python expression that produces exactly that shape for each literal.


def _native_literal(node: ast.AST) -> str:
    return ast.unparse(node)


def _fold_uniform(elts: Sequence[ast.AST], type_name: str, cons_prefix: str, elt_converter) -> str:
    rep = f"('{type_name}_{cons_prefix}nil',)"
    for elt in reversed(elts):
        rep = f"('{type_name}_{cons_prefix}cons', {elt_converter(elt)}, {rep})"
    return rep


def _record_repr(node: ast.Tuple, shape: tuple[str, ...], strategies: dict) -> str:
    parts = [convert_value(e, kind, strategies) for e, kind in zip(node.elts, shape)]
    return "('Tuple_mk', " + ", ".join(parts) + ")"


def _polymorphic_repr(node: ast.AST, type_name: str, cons_prefix: str) -> str:
    if not isinstance(node, (ast.Tuple, ast.List)):
        return _native_literal(node)
    return _fold_uniform(node.elts, type_name, cons_prefix, _native_literal)


def convert_value(node: ast.AST, aeon_type: str, strategies: dict[str, dict | None]) -> str:
    """Render ``node`` as the Python expression Aeon will see for ``aeon_type``."""
    if aeon_type in PRIMITIVES or aeon_type == "List":
        return _native_literal(node)
    if aeon_type == "Other":
        return _native_literal(node)

    if aeon_type == "Tuple":
        ts = strategies.get("tuple")
        if ts is None or ts["kind"] == "opaque":
            return _native_literal(node)
        if ts["kind"] == "polymorphic":
            return _polymorphic_repr(node, "Tuple", "t")
        if not isinstance(node, ast.Tuple):
            return _native_literal(node)
        if ts["kind"] == "uniform":
            elt_type = ts["elt"]
            return _fold_uniform(node.elts, "Tuple", "t", lambda e: convert_value(e, elt_type, strategies))
        if ts["kind"] == "record":
            return _record_repr(node, ts["shape"], strategies)
        if ts["kind"] == "nested":
            return _fold_uniform(node.elts, "Tuple", "t", lambda e: convert_value(e, "InnerTuple", strategies))
        return _native_literal(node)

    if aeon_type == "InnerTuple":
        ts = strategies.get("tuple")
        if ts is None or ts["kind"] != "nested" or not isinstance(node, ast.Tuple):
            return _native_literal(node)
        inner_elt = ts["inner"]
        return _fold_uniform(node.elts, "InnerTuple", "i", lambda e: convert_value(e, inner_elt, strategies))

    if aeon_type == "Dict":
        ds = strategies.get("dict")
        if ds is None or ds["kind"] in ("opaque",) or ds["kind"] != "uniform" or not isinstance(node, ast.Dict):
            return _native_literal(node)
        key_type, val_type = ds["key"], ds["val"]
        rep = "('Dict_dnil',)"
        for k, v in reversed(list(zip(node.keys, node.values))):
            if k is None:  # `**spread` syntax — not present in MBPP, but ast allows it
                continue
            rep = (
                f"('Dict_dcons', {convert_value(k, key_type, strategies)}, "
                f"{convert_value(v, val_type, strategies)}, {rep})"
            )
        return rep

    if aeon_type == "Set":
        ss = strategies.get("set")
        if ss is None or ss["kind"] in ("opaque",) or ss["kind"] != "uniform" or not isinstance(node, ast.Set):
            return _native_literal(node)
        elt_type = ss["elt"]
        return _fold_uniform(node.elts, "Set", "s", lambda e: convert_value(e, elt_type, strategies))

    # Polymorphic "list" handling (only the t446 case so far): the second
    # arg of t446 is a Python list, encoded as the inductive Seq cons-list.
    if aeon_type == "Seq":
        return _polymorphic_repr(node, "Seq", "s")

    return _native_literal(node)


# ---------------------------------------------------------------------------
# Signature inference (after strategies are chosen)
# ---------------------------------------------------------------------------


def _aeon_type_for(kind: str, strategies: dict[str, dict | None], position: str) -> str:
    """Map a literal kind to the Aeon type name for the signature.

    ``position`` is "arg" or "return" — used so the polymorphic Seq/Tuple
    naming stays consistent and ``List`` falls back to opaque ``List`` when no
    Set/Dict/Tuple strategy has been picked.
    """
    if kind in PRIMITIVES:
        return kind
    if kind == "Tuple":
        ts = strategies.get("tuple")
        if ts and ts["kind"] == "polymorphic":
            return "(Tuple a)"
        return "Tuple"
    if kind == "Dict":
        return "Dict"
    if kind == "Set":
        return "Set"
    if kind == "List":
        # In the polymorphic case t446 uses ``Seq a`` for its list arg.
        list_strategy = strategies.get("list")
        if list_strategy is not None and list_strategy.get("kind") == "polymorphic":
            return "(Seq a)"
        return "List"
    return "Int"  # last-resort fallback


# ---------------------------------------------------------------------------
# Assertion rewriting
# ---------------------------------------------------------------------------


def _literal_node(src: str) -> ast.expr:
    """Parse a generated Python expression string back into an AST node."""
    return ast.parse(src, mode="eval").body


class _Transformer(ast.NodeTransformer):
    """Rewrite a test assertion so it can run against an Aeon candidate."""

    def __init__(
        self,
        call: ast.Call,
        arg_types: list[str],
        ret_type: str,
        expected: ast.AST | None,
        strategies: dict[str, dict | None],
    ):
        self.call = call
        self.arg_types = arg_types
        self.ret_type = ret_type
        self.expected = expected
        self.strategies = strategies

    def visit(self, node: ast.AST) -> ast.AST:
        if node is self.expected:
            return _literal_node(convert_value(node, self.ret_type, self.strategies))
        return super().visit(node)

    def visit_Call(self, node: ast.Call) -> ast.AST:
        if node is self.call:
            if node.keywords:
                raise CodeGenError("test call uses keyword arguments")
            if len(node.args) != len(self.arg_types):
                raise CodeGenError("test call arity differs from inferred signature")
            result: ast.expr = ast.Name(id="f", ctx=ast.Load())
            for arg, kind in zip(node.args, self.arg_types):
                result = ast.Call(
                    func=result, args=[_literal_node(convert_value(arg, kind, self.strategies))], keywords=[]
                )
            return result
        self.generic_visit(node)
        return node

    def visit_Attribute(self, node: ast.Attribute) -> ast.AST:
        self.generic_visit(node)
        if isinstance(node.value, ast.Name) and node.value.id in ("math", "sys"):
            node.value = ast.Call(
                func=ast.Name(id="__import__", ctx=ast.Load()),
                args=[ast.Constant(value=node.value.id)],
                keywords=[],
            )
        return node


def transform_test(
    test_src: str,
    names: set[str],
    arg_kinds: list[str],
    ret_kind: str,
    strategies: dict[str, dict | None],
) -> str:
    """Return one MBPP assertion rewritten as a Python boolean expression."""
    tree = ast.parse(test_src.strip())
    if not tree.body or not isinstance(tree.body[0], ast.Assert):
        raise CodeGenError("test is not an assert statement")
    test = tree.body[0].test
    call = find_call(test, names)
    if call is None:
        raise CodeGenError("assertion does not call the target function")
    expected = find_expected(test, call) if ret_kind not in PRIMITIVES and ret_kind != "List" else None
    new_test = _Transformer(call, arg_kinds, ret_kind, expected, strategies).visit(test)
    ast.fix_missing_locations(new_test)
    return ast.unparse(new_test)


# ---------------------------------------------------------------------------
# File generation
# ---------------------------------------------------------------------------


def sanitize_arg_name(name: str, used: set[str]) -> str:
    candidate = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not candidate or not candidate[0].isalpha():
        candidate = "a_" + candidate
    while candidate in RESERVED or candidate in used:
        candidate += "_"
    used.add(candidate)
    return candidate


def escape_native(code: str) -> str:
    return code.replace("\\", "\\\\").replace('"', '\\"')


def comment_block(text: str) -> str:
    lines = text.strip().splitlines() or [""]
    return "\n".join("# " + line.rstrip() for line in lines)


def generate_file(problem: dict) -> str:
    task_id = problem["task_id"]
    code = problem["code"]
    prompt = problem.get("prompt", "").strip()
    test_list = problem["test_list"]

    defined: dict[str, list[str]] = {}
    for name, params in re.findall(r"def\s+(\w+)\s*\(([^)]*)\)", code):
        param_names = [p.split("=")[0].split(":")[0].strip() for p in params.split(",")]
        defined[name] = [p for p in param_names if p and p != "self"]
    if not defined:
        raise CodeGenError("no function definition found in canonical code")
    defined_names = set(defined)

    call = chosen_test = None
    for t in test_list:
        try:
            tree = ast.parse(t.strip())
        except SyntaxError:
            continue
        if tree.body and isinstance(tree.body[0], ast.Assert):
            c = find_call(tree.body[0].test, defined_names)
            if c is not None and c.args:
                call = c
                chosen_test = tree.body[0].test
                break
    if call is None or chosen_test is None:
        raise CodeGenError("could not find a usable test case")

    assert isinstance(call.func, ast.Name)
    fname = call.func.id
    arity = len(call.args)
    declared = defined.get(fname, [])
    arg_names = declared if len(declared) == arity else [f"a{i}" for i in range(arity)]

    arg_kinds = infer_arg_types(call)
    ret_kind = infer_return_type(chosen_test, call)
    strategies = analyze_strategies(problem)

    # A handful of problems (e.g. ``(4, 5, (7, 6, (2, 4)), 6, 8)``, dicts with
    # heterogeneous values, sets of tuples) have container literals we cannot
    # capture with a single inductive declaration. Mark those container kinds
    # as ``opaque`` so we still emit a valid file — the type just has no
    # constructors in the synthesis grammar.
    signature_kinds = set(arg_kinds) | {ret_kind}
    for kind, key in (("Tuple", "tuple"), ("Dict", "dict"), ("Set", "set")):
        if kind in signature_kinds and strategies.get(key) is None:
            strategies[key] = {"kind": "opaque"}

    arg_types = [_aeon_type_for(k, strategies, "arg") for k in arg_kinds]
    ret_type = _aeon_type_for(ret_kind, strategies, "return")

    # `type List` is needed whenever any declaration or signature mentions it.
    list_decl_needed = "List" in arg_types or ret_type == "List"
    ts = strategies.get("tuple")
    if ts is not None and ts.get("kind") == "record" and "List" in ts["shape"]:
        list_decl_needed = True
    ds = strategies.get("dict")
    if ds is not None and ds.get("kind") == "uniform" and "List" in (ds["key"], ds["val"]):
        list_decl_needed = True

    decls = declarations_for(strategies, list_decl_needed)

    conditions: list[str] = []
    for t in test_list:
        try:
            conditions.append(transform_test(t, defined_names, arg_kinds, ret_kind, strategies))
        except (CodeGenError, SyntaxError):
            continue
    if not conditions:
        raise CodeGenError("no usable test assertions")

    terms = " + ".join(f"(0 if ({c}) else 1)" for c in conditions)
    native_body = escape_native(f"float({terms})")

    used: set[str] = set()
    syn_args = [(sanitize_arg_name(n, used), t) for n, t in zip(arg_names, arg_types)]

    fitness_arg_type = ""
    for i, (_, t) in enumerate(syn_args):
        fitness_arg_type += f"(x{i}:{t}) -> "
    fitness_arg_type += ret_type

    synth_params = " ".join(f"({n}:{t})" for n, t in syn_args)

    header = comment_block(
        f"MBPP task {task_id}\n{prompt}\n\nSynthesis target: {fname} : "
        + " -> ".join(t for _, t in syn_args)
        + f" -> {ret_type}"
    )

    parts = [header, ""]
    if decls:
        parts.append("\n\n".join(decls))
        parts.append("")
    parts.append(f'def mbpp_fitness (f:{fitness_arg_type}) : Float = native "{native_body}"')
    parts.append("")
    parts.append("@hide(mbpp_fitness)")
    parts.append("@minimize_float(mbpp_fitness synth)")
    parts.append(f"def synth {synth_params} : {ret_type} = (?hole : {ret_type})")
    parts.append("")
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def load_dataset(source: str | None) -> list[dict]:
    if source and Path(source).exists():
        return json.loads(Path(source).read_text())
    url = source or SANITIZED_MBPP_URL
    with urllib.request.urlopen(url) as response:  # noqa: S310 - trusted URL
        return json.loads(response.read().decode("utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source",
        default=None,
        help="Path or URL to sanitized-mbpp.json (defaults to the MBPP repo).",
    )
    parser.add_argument(
        "--out",
        default="examples/MBPP",
        help="Directory to write the generated .ae files into.",
    )
    args = parser.parse_args()

    dataset = load_dataset(args.source)
    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)

    written = 0
    skipped: list[tuple[int, str]] = []
    for problem in dataset:
        task_id = problem["task_id"]
        try:
            content = generate_file(problem)
        except CodeGenError as exc:
            skipped.append((task_id, str(exc)))
            continue
        (out_dir / f"mbpp_{task_id}.ae").write_text(content)
        written += 1

    print(f"Wrote {written} files to {out_dir}/")
    if skipped:
        print(f"Skipped {len(skipped)} problems:")
        for task_id, reason in skipped:
            print(f"  task {task_id}: {reason}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
