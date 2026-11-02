"""Small, strict building blocks shared by the artifact translators."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def identifier(name: str) -> str:
    name = re.sub(r"[^a-zA-Z0-9_]", "_", name)
    if name in {
        "in",
        "if",
        "then",
        "else",
        "match",
        "with",
        "fun",
        "def",
        "let",
        "type",
        "inductive",
        "open",
        "import",
        "end",
        "forall",
        "native",
        "true",
        "false",
        "by",
        "class",
        "instance",
    }:
        name = "source_" + name
    return "v_" + name if name[:1].isdigit() else name


@dataclass
class Group:
    """Preserve the distinction between Lisp calls, lists, and rose trees."""

    bracket: str
    items: list[Any]


def sexprs(source: str) -> list[Any]:
    tokens = re.findall(r'"(?:\\.|[^"\\])*"|[()\[\]{}]|[^\s()\[\]{}]+', source)
    offset = 0

    def one():
        nonlocal offset
        token = tokens[offset]
        offset += 1
        if token in ("(", "[", "{"):
            end = {"(": ")", "[": "]", "{": "}"}[token]
            items = []
            while offset < len(tokens) and tokens[offset] != end:
                items.append(one())
            if offset == len(tokens):
                raise ValueError("Unclosed expression")
            offset += 1
            return Group(token, items)
        if token in (")", "]", "}"):
            raise ValueError("Unexpected closing delimiter")
        if re.fullmatch(r"-?\d+", token):
            return int(token)
        if token in ("#t", "#f"):
            return token == "#t"
        return token

    values = []
    while offset < len(tokens):
        values.append(one())
    return values


def merge_type(a, b):
    if a is None:
        return b
    if b is None:
        return a
    if isinstance(a, tuple) and isinstance(b, tuple) and a[0] == b[0]:
        return (a[0], merge_type(a[1], b[1]))
    if a != b:
        raise ValueError(f"Incompatible example types: {a!r} and {b!r}")
    return a


def value_type(value):
    if isinstance(value, bool):
        return "Bool"
    if isinstance(value, int):
        return "Int"
    if isinstance(value, list):
        return value_type(Group("[", value))
    if isinstance(value, Group):
        element = None
        if value.bracket == "[":
            for item in value.items:
                element = merge_type(element, value_type(item))
            return ("Seq", element)
        if value.bracket == "{":
            if value.items:
                element = value_type(value.items[0])
                for child in value.items[1:]:
                    child_type = value_type(child)
                    assert child_type[0] == "RoseTree"
                    element = merge_type(element, child_type[1])
            return ("RoseTree", element)
    raise ValueError(f"Not a ground value: {value!r}")


def ae_type(typ) -> str:
    if typ is None:
        raise ValueError("Example set does not determine an element type")
    if isinstance(typ, tuple):
        return f"({typ[0]} {ae_type(typ[1])})"
    return typ


def value(value, typ=None) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, int):
        return str(value) if value >= 0 else f"(0 - {-value})"
    if isinstance(value, list):
        return value_fn(Group("[", value), typ)
    if isinstance(value, Group):
        if value.bracket == "[":
            typ = typ or value_type(value)
            result = "(Seq.nil{" + ae_type(typ[1]) + "})"
            for item in reversed(value.items):
                result = f"(Seq.cons {value_fn(item, typ[1])} {result})"
            return result
        if value.bracket == "{":
            typ = typ or value_type(value)
            if not value.items:
                return "(RoseTree.empty{" + ae_type(typ[1]) + "})"
            return f"(RoseTree.node {value_fn(value.items[0], typ[1])} {value_fn(value.items[1:], ('Seq', typ))})"
    raise ValueError(f"Not a ground value: {value!r}")


value_fn = value


def example_program(types, examples, prelude="open Seq\nopen Maybe\nopen Pair\nopen Functional\n", name="target"):
    declarations = "".join(
        f"@example({name} {' '.join(value(x, t) for x, t in zip(args, types[:-1], strict=True))} = {value(out, types[-1])})\n"
        for args, out in examples
    )
    args = " ".join(f"(arg{i}:{ae_type(t)})" for i, t in enumerate(types[:-1]))
    return prelude + "\n" + declarations + f"def {name} {args} : {ae_type(types[-1])} := ?hole;\n"


class Corpus:
    def __init__(self, source_root: Path, output: Path):
        self.source_root = source_root
        self.output = output
        self.entries: list[dict] = []

    def add(self, suite: str, task: str, source: Path, code: str, **metadata):
        relative = Path(suite, task + ".ae")
        dest = self.output / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        origin = source.relative_to(self.source_root).as_posix()
        header = f"# Generated by scripts/paper_benchmarks; edit the translator, not this file.\n# Source: {origin}\n"
        dest.write_text("\n".join(line.rstrip() for line in (header + code).splitlines()).rstrip() + "\n")
        self.entries.append(
            {
                "suite": suite,
                "task": task,
                "source": origin,
                "source_sha256": digest(source),
                "path": relative.as_posix(),
                "sha256": digest(dest),
                **metadata,
            }
        )

    def save(self):
        self.output.mkdir(parents=True, exist_ok=True)
        (self.output / "manifest.json").write_text(json.dumps(self.entries, indent=2, sort_keys=True) + "\n")
