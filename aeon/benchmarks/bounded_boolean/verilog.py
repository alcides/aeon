"""Validated scalar combinational Verilog; never execute upstream tool code."""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Any

# JSON-compatible expression trees, shared syntax only (not solver translation).
Expr = list[Any]
TOKEN = re.compile(r"\s+|//[^\n]*|/\*[\s\S]*?\*/|1'[bB][01]|[01](?!\w)|[A-Za-z_][A-Za-z_0-9$]*|[(),;=~!&|^]")
IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9$]*\Z")


class VerilogError(ValueError):
    pass


@dataclass(frozen=True)
class Circuit:
    inputs: tuple[str, ...]
    outputs: tuple[str, ...]
    assignments: tuple[tuple[str, Expr], ...]  # topological order, reachable cone only
    unused: tuple[str, ...]
    y: tuple[str, ...]

    @property
    def x(self) -> tuple[str, ...]:
        return tuple(n for n in self.inputs if n not in self.y)


def references(expr: Expr) -> set[str]:
    if expr[0] == "var":
        return {expr[1]}
    return set().union(*(references(a) for a in expr[1:] if isinstance(a, list)))


def parse(source: str, y_source: str, filename: str = "<verilog>") -> Circuit:
    tokens = []
    offset = 0
    while offset < len(source):
        match = TOKEN.match(source, offset)
        if match is None:
            raise VerilogError(
                f"{filename}:{source.count(chr(10), 0, offset) + 1}: unsupported token {source[offset : offset + 20]!r}"
            )
        token = match.group()
        if not token.isspace() and not token.startswith(("//", "/*")):
            tokens.append((token, source.count("\n", 0, offset) + 1))
        offset = match.end()
    tokens.append(("<eof>", source.count("\n") + 1))
    pos = 0

    def error(message):
        raise VerilogError(f"{filename}:{tokens[pos][1]}: {message}")

    def take(expected=None):
        nonlocal pos
        token = tokens[pos][0]
        if expected is not None and token != expected:
            error(f"expected {expected}, found {token}")
        if token == "<eof>":
            error("unexpected end of source")
        pos += 1
        return token

    def identifier():
        token = tokens[pos][0]
        if not IDENT.fullmatch(token) or token in {"input", "output", "wire", "module", "endmodule", "assign"}:
            error(f"expected identifier, found {token}")
        return take()

    def names():
        result = [identifier()]
        while tokens[pos][0] == ",":
            take(",")
            result.append(identifier())
        if len(set(result)) != len(result):
            error("duplicate identifier")
        return result

    def expression(precedence=0):
        token = tokens[pos][0]
        if token in {"~", "!"}:
            take()
            left = ["not", expression(4)]
        elif token == "(":
            take()
            left = expression()
            take(")")
        elif token in {"0", "1", "1'b0", "1'b1", "1'B0", "1'B1"}:
            left = ["bool", take()[-1] == "1"]
        else:
            left = ["var", identifier()]
        operators = {"|": (1, "or"), "^": (2, "xor"), "&": (3, "and")}
        while tokens[pos][0] in operators and operators[tokens[pos][0]][0] > precedence:
            level, op = operators[take()]
            left = [op, left, expression(level)]
        return left

    take("module")
    identifier()
    take("(")
    ports = names()
    take(")")
    take(";")
    declarations: dict[str, str] = {}
    inputs, outputs = [], []
    assignments: dict[str, Expr] = {}
    while tokens[pos][0] != "endmodule":
        kind = take()
        if kind in {"input", "output", "wire"}:
            for name in names():
                if name in declarations:
                    error(f"duplicate declaration {name}")
                declarations[name] = kind
                if kind == "input":
                    inputs.append(name)
                if kind == "output":
                    outputs.append(name)
        elif kind == "assign":
            name = identifier()
            take("=")
            value = expression()
            if name in assignments:
                error(f"multiple drivers for {name}")
            assignments[name] = value
        else:
            error(f"unsupported statement {kind}")
        take(";")
    take("endmodule")
    if tokens[pos][0] != "<eof>":
        error("multiple modules or trailing syntax")
    if set(ports) != set(inputs + outputs) or len(outputs) != 1:
        error("expected declared input ports and exactly one relation output")
    for name, expr in assignments.items():
        if declarations.get(name) not in {"wire", "output"}:
            error(f"assignment to undeclared signal or input {name}")
        for ref in references(expr):
            if ref not in declarations:
                error(f"unknown signal {ref}")
            if ref not in inputs and ref not in assignments:
                error(f"undriven signal {ref}")
    # Validate even unreachable assigned logic for cycles. Unused, undriven wire
    # declarations are recorded, not turned into extra nondeterministic inputs.
    ordered: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set(inputs)

    def visit(name):
        if name in visited:
            return
        if name in visiting:
            error(f"combinational cycle at {name}")
        if name not in assignments:
            error(f"undriven relation output {name}")
        visiting.add(name)
        for dependency in sorted(references(assignments[name])):
            visit(dependency)
        visiting.remove(name)
        visited.add(name)
        ordered.append(name)

    visit(outputs[0])
    cone = list(ordered)
    reachable = set(cone) | set().union(*(references(assignments[n]) for n in cone))
    for name in assignments:
        visit(name)
    listed = y_source.split()
    if len(set(listed)) != len(listed) or any(n not in inputs for n in listed):
        error("Y list must contain distinct declared inputs")
    # Preserve module port order; the list selects Y, it does not create ports.
    ordered_inputs = tuple(p for p in ports if p in inputs)
    y = tuple(p for p in ordered_inputs if p in listed)
    return Circuit(
        ordered_inputs,
        tuple(outputs),
        tuple((n, assignments[n]) for n in cone),
        tuple(sorted(set(declarations) - reachable)),
        y,
    )


def evaluate(circuit: Circuit, values: dict[str, bool]) -> bool:
    """Small-domain reference interpreter, independent of Aeon and Z3."""
    env = dict(values)

    def run(expr):
        op, *args = expr
        if op == "bool":
            return args[0]
        if op == "var":
            return env[args[0]]
        if op == "not":
            return not run(args[0])
        a, b = run(args[0]), run(args[1])
        return (a and b) if op == "and" else (a or b) if op == "or" else a != b

    for name, expr in circuit.assignments:
        env[name] = run(expr)
    return env[circuit.outputs[0]]
