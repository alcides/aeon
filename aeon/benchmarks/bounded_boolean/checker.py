"""Independent source-relation and emitted-CNF checks; no synthesis imports.

Verilog -> Z3 and Core -> small Boolean syntax are separate translation paths
from Aeon's compiler VCs and the bounded backend's templates/normalizer.
"""

from __future__ import annotations

from itertools import product
from typing import Any

import z3

from aeon.benchmarks.bounded_boolean.corpus import ae_name
from aeon.benchmarks.bounded_boolean.verilog import Circuit, Expr, evaluate
from aeon.core.multiplicity import MOmega
from aeon.core.terms import Abstraction, Annotation, Application, Let, Literal, Rec, Term, TypeApplication, Var
from aeon.core.types import AbstractionType, RefinedType, t_bool
from aeon.utils.name import Name


class CheckFailure(ValueError):
    def __init__(self, status: str, reason: str):
        self.status = status
        super().__init__(reason)


def core_expression(term: Term, variables: dict[Name, Expr], limit: int = 20_000) -> Expr:
    visited = 0

    def convert(t, env):
        nonlocal visited
        visited += 1
        if visited > limit:
            raise CheckFailure("resource_limit", "core expression size limit exceeded")
        if isinstance(t, Annotation):
            return convert(t.expr, env)
        if isinstance(t, Literal) and t.type == t_bool and type(t.value) is bool:
            return ["bool", t.value]
        if isinstance(t, Var) and t.name in env:
            return env[t.name]
        if isinstance(t, Let) and t.multiplicity is MOmega:
            value = convert(t.var_value, env)
            return convert(t.body, env | {t.var_name: value})
        args = []
        head = t
        while isinstance(head, (Application, TypeApplication)):
            if isinstance(head, Application):
                args.insert(0, head.arg)
                head = head.fun
            else:
                head = head.body
        ops = {"&&": "and", "||": "or", "!": "not", "!=": "xor", "==": "eq", "-->": "implies"}
        if isinstance(head, Var) and head.name.id == 0 and head.name.name in ops:
            op = ops[head.name.name]
            if len(args) == (1 if op == "not" else 2):
                return [op, *(convert(a, env) for a in args)]
        raise CheckFailure(
            "structural_failure",
            "expected pure Boolean syntax over declared inputs; found helper, witness, hole or unsupported term",
        )

    try:
        return convert(term, variables)
    except RecursionError as exc:
        raise CheckFailure("resource_limit", "core expression recursion limit exceeded") from exc


def cnf(expr: Expr, input_count: int) -> list[list[int]]:
    """Independent CNF count convention: true=[], false=[[]]. No distribution."""
    visits = 0

    def tick():
        nonlocal visits
        visits += 1
        if visits > 20_000:
            raise CheckFailure("resource_limit", "CNF normalization size limit exceeded")

    def literal(node, negative=False):
        tick()
        if node[0] == "not":
            return literal(node[1], not negative)
        if node[0] == "bool":
            return ([], node[1] != negative)
        if node[0] == "var" and type(node[1]) is int and 0 <= node[1] < input_count:
            return ([(-1 if negative else 1) * (node[1] + 1)], False)
        raise CheckFailure("structural_failure", "CNF literal is not a permitted Boolean input")

    def disjunction(node):
        tick()
        if node[0] != "or":
            return literal(node)
        a, at = disjunction(node[1])
        b, bt = disjunction(node[2])
        values = set(a + b)
        return (list(values), at or bt or any(-v in values for v in values))

    def conjunction(node):
        tick()
        if node[0] == "and":
            return conjunction(node[1]) + conjunction(node[2])
        values, tautology = disjunction(node)
        return [] if tautology else [tuple(sorted(set(values)))]

    try:
        clauses = conjunction(expr)
    except RecursionError as exc:
        raise CheckFailure("resource_limit", "CNF recursion limit exceeded") from exc
    if () in clauses:
        return [[]]
    return [list(c) for c in sorted(set(clauses))]


def _definitions(program: Term):
    result = {}
    while isinstance(program, (Rec, Let)):
        result[program.var_name.name] = program
        program = program.body
    return result


def _body(definition, params: tuple[str, ...]):
    if not isinstance(definition, Rec):
        raise CheckFailure("type_failure", "missing typed definition")
    body, ty = definition.var_value, definition.var_type
    env = {}
    for i, _ in enumerate(params):
        while isinstance(body, Annotation):
            body = body.expr
        base = (
            ty.var_type.type
            if isinstance(ty, AbstractionType) and isinstance(ty.var_type, RefinedType)
            else getattr(ty, "var_type", None)
        )
        if (
            not isinstance(body, Abstraction)
            or not isinstance(ty, AbstractionType)
            or base != t_bool
            or ty.multiplicity is not MOmega
        ):
            raise CheckFailure("type_failure", "output signature must have exactly the declared Boolean inputs")
        env[body.var_name] = ["var", i]
        body, ty = body.body, ty.type
    if (ty.type if isinstance(ty, RefinedType) else ty) != t_bool:
        raise CheckFailure("type_failure", "output signature must return Bool")
    return core_expression(body, env)


def extract(program: Term, circuit: Circuit, bound: int) -> dict[str, list[list[int]]]:
    definitions = _definitions(program)
    outputs = {}
    for name in circuit.y:
        expr = _body(definitions.get(f"choose_{ae_name(name)}"), circuit.x)
        clauses = cnf(expr, len(circuit.x))
        if len(clauses) > bound:
            raise CheckFailure("bound_violation", f"{name}: {len(clauses)} clauses exceed K={bound}")
        outputs[name] = clauses
    return outputs


def z3_expression(expr: Expr, env: dict, context) -> z3.BoolRef:
    op, *args = expr
    if op == "var":
        return env[args[0]]
    if op == "bool":
        return z3.BoolVal(args[0], context)
    values = [z3_expression(a, env, context) for a in args]
    operations = {
        "not": z3.Not,
        "and": z3.And,
        "or": z3.Or,
        "xor": z3.Xor,
        "eq": lambda a, b: a == b,
        "implies": z3.Implies,
    }
    return operations[op](*values)


def relation(circuit: Circuit, values: dict, context) -> z3.BoolRef:
    env = dict(values)
    for name, expr in circuit.assignments:
        env[name] = z3_expression(expr, env, context)
    return env[circuit.outputs[0]]


def check_import(program: Term, circuit: Circuit, timeout_ms: int = 5000) -> str:
    """Prove the generated Aeon relation equivalent to the original circuit."""
    expr = _body(_definitions(program).get("relation"), circuit.inputs)
    context = z3.Context()
    inputs = {n: z3.Bool(f"input_{i}", context) for i, n in enumerate(circuit.inputs)}
    solver = z3.Solver(ctx=context)
    solver.set(timeout=timeout_ms)
    solver.add(z3_expression(expr, dict(enumerate(inputs.values())), context) != relation(circuit, inputs, context))
    status = solver.check()
    return "equivalent" if status == z3.unsat else "translation_failure" if status == z3.sat else "unknown"


def check(circuit: Circuit, outputs: dict, bound: int, timeout_ms: int = 5000) -> dict[str, Any]:
    """Verify a portable CNF certificate against the original partial relation."""
    if type(bound) is not int or bound < 0 or set(outputs) != set(circuit.y):
        raise CheckFailure("structural_failure", "wrong output names or clause bound")
    normalized = {}
    for name, clauses in outputs.items():
        if not isinstance(clauses, list) or len(clauses) > 20_000:
            raise CheckFailure("structural_failure", "invalid CNF certificate")
        clean = []
        for clause in clauses:
            if not isinstance(clause, list) or any(
                type(v) is not int or not 1 <= abs(v) <= len(circuit.x) for v in clause
            ):
                raise CheckFailure("structural_failure", "literal refers to a forbidden input")
            literals = set(clause)
            if not any(-v in literals for v in literals):
                clean.append(tuple(sorted(literals)))
        normal = [[]] if () in clean else [list(c) for c in sorted(set(clean))]
        if len(normal) > bound:
            raise CheckFailure("bound_violation", f"{name} exceeds K={bound}")
        normalized[name] = normal
    context = z3.Context()
    inputs = {n: z3.Bool(f"input_{i}", context) for i, n in enumerate(circuit.inputs)}
    x = [inputs[n] for n in circuit.x]
    chosen = dict(inputs)
    for name, clauses in normalized.items():
        disjunctions = [
            z3.Or([x[v - 1] if v > 0 else z3.Not(x[-v - 1]) for v in clause]) if clause else z3.BoolVal(False, context)
            for clause in clauses
        ]
        chosen[name] = z3.And(disjunctions) if disjunctions else z3.BoolVal(True, context)
    solver = z3.Solver(ctx=context)
    solver.set(timeout=max(1, timeout_ms))
    solver.add(relation(circuit, inputs, context), z3.Not(relation(circuit, chosen, context)))
    status = solver.check()
    counts = {n: len(cs) for n, cs in normalized.items()}
    result = {
        "status": "verified_solved" if status == z3.unsat else "semantic_failure" if status == z3.sat else "unknown",
        "clauses": counts,
        "total_clauses": sum(counts.values()),
        "max_clauses": max(counts.values(), default=0),
        "literal_count": sum(len(c) for cs in normalized.values() for c in cs),
    }
    if status == z3.sat:
        model = solver.model()
        result["counterexample"] = {n: z3.is_true(model.eval(v, model_completion=True)) for n, v in inputs.items()}
    if status == z3.unknown:
        result["reason"] = solver.reason_unknown()
    # Cross-check small domains with a Boolean interpreter, not a second call
    # to the same solver translation. No exponential work on large instances.
    if status != z3.unknown and len(circuit.inputs) <= 8:
        valid = True
        for bits in product((False, True), repeat=len(circuit.inputs)):
            values = dict(zip(circuit.inputs, bits))
            xs = [values[n] for n in circuit.x]
            ys = {
                n: all(any(xs[abs(v) - 1] == (v > 0) for v in clause) for clause in cs) for n, cs in normalized.items()
            }
            if evaluate(circuit, values) and not evaluate(circuit, values | ys):
                valid = False
                break
        if valid != (status == z3.unsat):
            raise CheckFailure("validation_error", "independent truth table and SMT checker disagree")
        result["exhaustive_checked"] = True
    return result


def exhaustive_status(circuit: Circuit, bound: int, limit: int = 10_000) -> str:
    """Tiny independent finite-family oracle; never infer UNSAT from a limit."""
    from itertools import combinations
    from math import comb

    n = len(circuit.x)
    if n > 3 or len(circuit.y) > 2 or bound < 0:
        return "not_checked"
    # One of absent / positive / negative for every input in each clause.
    clauses = [tuple(sign * (i + 1) for i, sign in enumerate(signs) if sign) for signs in product((0, 1, -1), repeat=n)]
    k = min(bound, len(clauses))
    family_size = sum(comb(len(clauses), size) for size in range(k + 1))
    if family_size ** len(circuit.y) > limit:
        return "not_checked"
    functions = [selected for size in range(k + 1) for selected in combinations(clauses, size)]
    valuations = [dict(zip(circuit.inputs, values)) for values in product((False, True), repeat=len(circuit.inputs))]
    for vector in product(functions, repeat=len(circuit.y)):
        valid = True
        for values in valuations:
            if not evaluate(circuit, values):
                continue
            xs = [values[n] for n in circuit.x]
            outputs = {
                n: all(any(xs[abs(v) - 1] == (v > 0) for v in c) for c in cs) for n, cs in zip(circuit.y, vector)
            }
            if not evaluate(circuit, values | outputs):
                valid = False
                break
        if valid:
            return "feasible"
    return "bounded_unsat"
