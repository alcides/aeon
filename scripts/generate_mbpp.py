#!/usr/bin/env python3
"""Generate one self-contained Aeon synthesis benchmark per MBPP problem.

MBPP (Mostly Basic Programming Problems, Google Research) ships ~1000 short
Python problems, each with a prompt, a canonical solution and a handful of
`assert` test cases. This script turns the sanitized subset into individual
`.ae` files under `examples/MBPP/`, one per problem.

Each generated file is fully self-contained:
  * the prompt is kept as a comment,
  * the problem's `test_list` assertions are embedded into a `native` fitness
    function that returns the number of failing assertions as a Float,
  * a `?hole` of the inferred signature is the synthesis target, driven by
    `@minimize_float`.

Argument and return types are inferred heuristically from the literals in the
first usable test case. Python values that Aeon cannot express natively
(tuples, dicts, sets, and anything else) get an opaque custom datatype
declared at the top of the file (`Tuple`, `Dict`, `Set`, `Obj`).

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

# Python builtins that are available inside a `native` expression without import.
SAFE_BUILTINS = {
    "set",
    "sorted",
    "list",
    "len",
    "str",
    "int",
    "float",
    "abs",
    "round",
    "sum",
    "min",
    "max",
    "tuple",
    "dict",
    "frozenset",
    "bool",
    "all",
    "any",
}


class CodeGenError(Exception):
    """Raised when a problem cannot be turned into a valid Aeon file."""


def classify_literal(node: ast.AST) -> tuple[str, bool]:
    """Map a Python literal AST node to an Aeon type name.

    Returns (type_name, is_custom). Custom types are opaque datatypes that
    must be declared at the top of the generated file.
    """
    if isinstance(node, ast.Constant):
        v = node.value
        if isinstance(v, bool):
            return "Bool", False
        if isinstance(v, int):
            return "Int", False
        if isinstance(v, float):
            return "Float", False
        if isinstance(v, str):
            return "String", False
        return "Obj", True
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        return classify_literal(node.operand)
    if isinstance(node, ast.List):
        return "List", False
    if isinstance(node, ast.Tuple):
        return "Tuple", True
    if isinstance(node, ast.Dict):
        return "Dict", True
    if isinstance(node, ast.Set):
        return "Set", True
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        name = node.func.id
        if name == "set":
            return "Set", True
        if name in ("list", "sorted"):
            return "List", False
        if name == "tuple":
            return "Tuple", True
        if name == "dict":
            return "Dict", True
    return "Obj", True


def _contains(node: ast.AST, target: ast.AST) -> bool:
    return any(n is target for n in ast.walk(node))


def find_call(test: ast.AST, names: set[str]) -> ast.Call | None:
    """Locate the call to one of the problem's functions inside an assert.

    MBPP canonical solutions often define helper functions before the entry
    point, so we match against every name defined in the snippet rather than
    assuming the first `def`.
    """
    for n in ast.walk(test):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in names:
            return n
    return None


def infer_return_type(test: ast.AST, call: ast.Call) -> tuple[str, bool]:
    """Infer the function's return type from how its call result is used."""
    if test is call:
        return "Bool", False
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return "Bool", False
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        left, right = test.left, test.comparators[0]
        if _contains(left, call):
            wrapper, other = left, right
        elif _contains(right, call):
            wrapper, other = right, left
        else:
            return "Int", False
        if wrapper is call:
            return classify_literal(other)
        if isinstance(wrapper, ast.Call) and isinstance(wrapper.func, ast.Name):
            wf = wrapper.func.id
            if wf in ("set", "sorted", "list", "len"):
                return "List", False
            if wf == "str":
                return "String", False
            if wf in ("int", "abs", "round", "sum", "min", "max"):
                return "Int", False
            if wf == "float":
                return "Float", False
            if wf == "tuple":
                return "Tuple", True
            if wf == "dict":
                return "Dict", True
        return classify_literal(other)
    if isinstance(test, ast.Call) and isinstance(test.func, ast.Attribute):
        if test.func.attr == "isclose":
            return "Float", False
    return "Int", False


def infer_arg_types(call: ast.Call) -> tuple[list[str], set[str]]:
    """Infer argument types from the literals passed in a test call."""
    types: list[str] = []
    custom: set[str] = set()
    for arg in call.args:
        t, is_custom = classify_literal(arg)
        types.append(t)
        if is_custom:
            custom.add(t)
    return types, custom


class _Transformer(ast.NodeTransformer):
    """Rewrite a test assertion so it can run against an Aeon candidate.

    * `fname(a, b, c)` becomes the curried call `f(a)(b)(c)`.
    * `math.x` / `sys.x` become `__import__('math').x` / `__import__('sys').x`
      so they resolve inside Aeon's `native` evaluation namespace.
    """

    def __init__(self, fname: str):
        self.fname = fname

    def visit_Call(self, node: ast.Call) -> ast.AST:
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id == self.fname:
            if node.keywords:
                raise CodeGenError("test call uses keyword arguments")
            result: ast.expr = ast.Name(id="f", ctx=ast.Load())
            for arg in node.args:
                result = ast.Call(func=result, args=[arg], keywords=[])
            return result
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


def transform_test(test_src: str, fname: str, names: set[str]) -> str:
    """Return a Python boolean expression equivalent to one MBPP assertion."""
    tree = ast.parse(test_src.strip())
    if not tree.body or not isinstance(tree.body[0], ast.Assert):
        raise CodeGenError("test is not an assert statement")
    test = tree.body[0].test
    if find_call(test, names) is None:
        raise CodeGenError("assertion does not call the target function")
    new_test = _Transformer(fname).visit(test)
    ast.fix_missing_locations(new_test)
    return ast.unparse(new_test)


def sanitize_arg_name(name: str, used: set[str]) -> str:
    """Make a Python parameter name safe to use as an Aeon identifier."""
    candidate = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not candidate or not candidate[0].isalpha():
        candidate = "a_" + candidate
    while candidate in RESERVED or candidate in used:
        candidate += "_"
    used.add(candidate)
    return candidate


def escape_native(code: str) -> str:
    """Escape a Python snippet for embedding inside an Aeon `native "..."`."""
    return code.replace("\\", "\\\\").replace('"', '\\"')


def comment_block(text: str) -> str:
    """Render arbitrary text as a block of Aeon `#` comments."""
    lines = text.strip().splitlines() or [""]
    return "\n".join("# " + line.rstrip() for line in lines)


def generate_file(problem: dict) -> str:
    """Produce the contents of one `.ae` file for an MBPP problem."""
    task_id = problem["task_id"]
    code = problem["code"]
    prompt = problem.get("prompt", "").strip()
    test_list = problem["test_list"]

    # MBPP canonical code often defines helpers before the entry point, so
    # collect every definition and let the tests tell us which one is called.
    defined: dict[str, list[str]] = {}
    for name, params in re.findall(r"def\s+(\w+)\s*\(([^)]*)\)", code):
        param_names = [p.split("=")[0].split(":")[0].strip() for p in params.split(",")]
        defined[name] = [p for p in param_names if p and p != "self"]
    if not defined:
        raise CodeGenError("no function definition found in canonical code")
    defined_names = set(defined)

    # Find a test we can use to infer the signature.
    call = None
    chosen_test = None
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
    if len(declared) == arity:
        arg_names = declared
    else:
        arg_names = [f"a{i}" for i in range(arity)]

    arg_types, custom = infer_arg_types(call)
    ret_type, ret_custom = infer_return_type(chosen_test, call)
    if ret_custom:
        custom.add(ret_type)

    # Every non-primitive type used in the signature needs a local opaque
    # declaration. `List` in particular must be declared monomorphically here,
    # otherwise elaborating a `?hole : List` unifies against the parametric
    # `List a` from the standard library and loops.
    PRIMITIVES = {"Int", "Bool", "Float", "String"}
    custom |= ({ret_type} | set(arg_types)) - PRIMITIVES

    # Transform every assertion; skip any that do not fit the inferred shape.
    conditions: list[str] = []
    for t in test_list:
        try:
            conditions.append(transform_test(t, fname, defined_names))
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

    type_decls = "".join(f"type {t}\n" for t in sorted(custom))

    synth_params = " ".join(f"({n}:{t})" for n, t in syn_args)

    header = comment_block(
        f"MBPP task {task_id}\n{prompt}\n\n"
        f"Synthesis target: {fname} : " + " -> ".join(t for _, t in syn_args) + f" -> {ret_type}"
    )

    parts = [header, ""]
    if type_decls:
        parts.append(type_decls.rstrip())
        parts.append("")
    parts.append(f'def mbpp_fitness (f:{fitness_arg_type}) : Float = native "{native_body}"')
    parts.append("")
    parts.append("@hide(mbpp_fitness)")
    parts.append("@minimize_float(mbpp_fitness synth)")
    parts.append(f"def synth {synth_params} : {ret_type} = (?hole : {ret_type})")
    parts.append("")
    return "\n".join(parts)


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
