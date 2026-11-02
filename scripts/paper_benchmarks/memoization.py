"""Finite residual-language memoization tasks from SynMem's constraint ASTs.

Read the C++ constructor DSL as data; never build or execute the Docker image.
The generated keys may merge prefixes only when their valid completions agree.
This ports the memoization partition subproblem, not SynMem's local-objective
synthesis or its unbounded verification/performance experiment.
"""

from __future__ import annotations

import itertools
import re
from dataclasses import dataclass, field

from .common import identifier, value


def arguments(text):
    result = []
    depth = 0
    start = 0
    for i, char in enumerate(text):
        if char in "({":
            depth += 1
        if char in ")}":
            depth -= 1
        if char == "," and depth == 0:
            result.append(text[start:i].strip())
            start = i + 1
    result.append(text[start:].strip())
    return result


@dataclass
class Problem:
    names: dict = field(default_factory=dict)
    nodes: dict = field(default_factory=dict)
    operators: dict = field(default_factory=dict)
    constraints: list = field(default_factory=list)

    def literal(self, text):
        text = text.strip()
        if re.fullmatch(r"-?\d+", text):
            return int(text)
        match = re.fullmatch(r"(\w+)\s*\+\s*INF|VAR_TO_VALUE\(\s*(\w+)\s*\)", text)
        if match:
            return ("var", match[1] or match[2])
        if text == "INF":
            return 100000000
        if text == "-INF":
            return -100000000
        raise ValueError(f"Unknown constructor literal: {text}")

    def node(self, text):
        text = re.sub(r"->deepcopy\(\s*\)", "", text).strip()
        if text in self.nodes:
            return self.nodes[text]
        match = re.fullmatch(r"new (constval|atom_term|reduce_term)\((.*)\)", text, re.S)
        if not match:
            raise ValueError(text)
        kind, body = match.groups()
        args = arguments(body)
        if kind == "constval":
            return self.literal(args[0])
        op = self.operator(args[0])
        if kind == "atom_term":
            return (op, *(self.node(x) for x in arguments(args[1].strip()[1:-1])))
        return ("reduce", op, self.node(args[1]), self.node(args[2]), args[3], self.node(args[4]))

    def operator(self, text):
        match = re.fullmatch(r'string_to_op\(\s*"(\w+)"\s*\)', text)
        return match[1] if match else self.operators[text]

    @classmethod
    def parse(cls, text):
        result = cls()
        # Only the constructor body. Copy constructors and enumerators are not specs.
        for match in re.finditer(
            r"\b(\w+)\s*=\s*(new_parameter_list\([^;]+|new_var_list\([^;]+|new_parameter\([^;]+|new_var\([^;]+|string_to_op\([^;]+|new (?:constval|atom_term|reduce_term)\([^;]+);|add_constraint\(\s*(\w+)\s*\)\s*;",
            text,
        ):
            name, rhs, constraint = match.groups()
            if constraint:
                result.constraints.append(result.nodes[constraint])
                continue
            rhs = rhs.strip()
            declaration = re.fullmatch(r"(new_\w+)\((.*)\)", rhs, re.S)
            if declaration:
                kind, body = declaration.groups()
                args = arguments(body)
                domain = args[-1].strip()
                domain = domain[len("make_pair(") : -1] if domain.startswith("make_pair(") else domain[1:-1]
                result.names[name] = (
                    kind,
                    args[0].strip('" '),
                    result.literal(args[1]) if kind.endswith("_list") else None,
                    tuple(result.literal(x) for x in arguments(domain)),
                )
            elif rhs.startswith("string_to_op"):
                result.operators[name] = result.operator(rhs)
            else:
                result.nodes[name] = result.node(rhs)
        assert result.constraints and result.names
        return result


def evaluate(node, env):
    if isinstance(node, int):
        return node
    op, *args = node
    if op == "var":
        return env[args[0]]
    if op == "reduce":
        operator, lower, upper, variable, body = args
        values = [evaluate(body, {**env, variable: i}) for i in range(evaluate(lower, env), evaluate(upper, env) + 1)]
        if operator == "And":
            return int(all(values))
        if operator == "Add":
            return sum(values)
        raise ValueError(operator)
    values = [evaluate(x, env) for x in args]
    if op.startswith("Call_"):
        xs, index = values
        # SynMem's environment returns its -INF sentinel for missing entries.
        return xs[index] if 0 <= index < len(xs) else -100000000
    a, b = values
    if op == "Add":
        return a + b
    if op == "Sub":
        return a - b
    if op == "Mult":
        return a * b
    if op == "Less":
        return int(a < b)
    if op == "Equal":
        return int(a == b)
    if op == "And":
        return a & b
    if op == "Or":
        return int(bool(a) or bool(b))
    raise ValueError(op)


def states(problem, instance):
    """Exhaust all assignments and prefixes of one small, reproducible instance."""
    env = {}
    params = []
    dimensions = []
    decision_lists = []
    for name, (kind, label, length, domain) in problem.names.items():
        if kind == "new_parameter":
            x = 3 if label == "n" else 2 if label == "m" else instance + 1
            env[name] = x
            params.append(x)
        elif kind == "new_parameter_list":
            # Exactly the declared length; missing indices use the source sentinel.
            xs = [(i + instance) % 3 for i in range(evaluate(length, env))]
            env[name] = xs
            params.append(xs)
        elif kind == "new_var_list":
            size = evaluate(length, env)
            lo, hi = (evaluate(x, env) for x in domain)
            assert 0 <= size <= 4 and 0 <= lo <= hi <= 3
            dimensions.extend([list(range(lo, hi + 1))] * size)
            decision_lists.append((name, size))
    accepted = {}
    for assignment in itertools.product(*dimensions):
        offset = 0
        local = dict(env)
        for name, size in decision_lists:
            local[name] = assignment[offset : offset + size]
            offset += size
        accepted[assignment] = all(evaluate(node, local) for node in problem.constraints)
    classes = {}
    result = []
    for depth in range(len(dimensions) + 1):
        for prefix in itertools.product(*dimensions[:depth]):
            residual = tuple(accepted[prefix + suffix] for suffix in itertools.product(*dimensions[depth:]))
            signature = (depth, residual)
            if signature not in classes:
                classes[signature] = len(classes)
            result.append((list(prefix), classes[signature]))
    return params, result


def synmem(corpus):
    for path in sorted((corpus.source_root / "synmem/benchmarks").glob("my*.h")):
        text = re.sub(r"//[^\n]*", "", path.read_text())
        classes = list(re.finditer(r"class\s+(prob\d+_\w+)\s*:\s*public example", text))
        for i, match in enumerate(classes):
            problem = Problem.parse(text[match.end() : classes[i + 1].start() if i + 1 < len(classes) else len(text)])
            params = [
                (identifier(label), "(Seq Int)" if kind.endswith("_list") else "Int")
                for kind, label, _, _ in problem.names.values()
                if kind.startswith("new_parameter")
            ]
            signature = " -> ".join([*(f"({name}:{typ})" for name, typ in params), "(prefix:(Seq Int))", "Int"])
            code = "open Seq\nopen Pair\nopen Memoization\n\n"
            scores = []
            total_states = 0
            for instance in range(3):
                inputs, cases = states(problem, instance)
                total_states += len(cases)
                values = [value(x, ("Seq", "Int") if isinstance(x, list) else "Int") for x in inputs]
                fixture = "(Seq.nil{(Pair (Seq Int) Int)})"
                for prefix, residual in reversed(cases):
                    fixture = f"(Seq.cons (Pair.mk {value(prefix, ('Seq', 'Int'))} {residual}) {fixture})"
                code += f"def cases{instance} : (Seq (Pair (Seq Int) Int)) := {fixture};\n"
                scores.append(f"(Memoization.partitionScore (candidate {' '.join(values)}) cases{instance})")
            code += f"\ndef corpusScore (candidate:{signature}) : Int := " + " + ".join(scores) + ";\n"
            code += "@minimize_int(corpusScore target)\n"
            code += (
                "def target " + " ".join(f"({n}:{t})" for n, t in params) + " (prefix:(Seq Int)) : Int := ?memoKey;\n"
            )
            corpus.add(
                "synmem",
                match[1],
                path,
                code,
                specification="bounded-memoization-partition",
                original_benchmark=path.stem,
                instances=3,
                states=total_states,
                limitation="Finite residual equivalence; excludes local-objective synthesis and unbounded verification.",
                decision_order=[name for name, (kind, *_) in problem.names.items() if kind == "new_var_list"],
            )
