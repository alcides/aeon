"""One existential function model for all holes and shared obligations."""

from __future__ import annotations

import z3

from aeon.core.terms import If, Literal, Term, Var
from aeon.core.types import t_bool, t_float, t_int
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.joint import JointCandidate
from aeon.synthesis.modules.sygus.solver import _apply_op, _num_literal
from aeon.synthesis.solver_problem import SolverProblem
from aeon.verification.smt import translate_liq


def _sort(base):
    return {t_int: z3.IntSort(), t_bool: z3.BoolSort(), t_float: z3.RealSort()}[base]


def _base(sort):
    return {z3.Z3_INT_SORT: t_int, z3.Z3_BOOL_SORT: t_bool, z3.Z3_REAL_SORT: t_float}[sort.kind()]


def _interpret(model, function, arguments):
    model.eval(
        function(*[z3.Const(f"model_completion_{i}", arg.sort()) for i, arg in enumerate(arguments)]),
        model_completion=True,
    )
    interpretation = model[function]
    if interpretation is None:
        return model.eval(function(*arguments), model_completion=True)
    value = z3.substitute_vars(interpretation.else_value(), *arguments)
    for index in range(interpretation.num_entries()):
        entry = interpretation.entry(index)
        guard = z3.And(*[arg == entry.arg_value(i) for i, arg in enumerate(arguments)])
        value = z3.If(guard, entry.value(), value)
    return z3.simplify(value)


def _decode(node, variables, model, expanding=frozenset()):
    if z3.is_true(node) or z3.is_false(node):
        return Literal(z3.is_true(node), t_bool)
    if z3.is_int_value(node):
        return _num_literal(node.as_long(), t_int)
    if z3.is_rational_value(node):
        numerator, denominator = node.numerator_as_long(), node.denominator_as_long()
        if denominator == 1:
            return _num_literal(numerator, t_float)
        return _apply_op("/", t_float, _num_literal(numerator, t_float), _num_literal(denominator, t_float))
    if node in variables:
        return Var(variables[node])
    if not z3.is_app(node):
        raise ValueError(f"Unsupported Z3 result {node}")
    kind = node.decl().kind()
    if kind == z3.Z3_OP_UNINTERPRETED:
        function = node.decl()
        if function in expanding:
            raise ValueError("Recursive Z3 interpretation")
        return _decode(_interpret(model, function, node.children()), variables, model, expanding | {function})
    children = [_decode(child, variables, model, expanding) for child in node.children()]
    if kind == z3.Z3_OP_ITE:
        return If(*children)
    if kind == z3.Z3_OP_UMINUS:
        base = _base(node.sort())
        return _apply_op("-", base, _num_literal(0, base), children[0])
    operators = {
        z3.Z3_OP_ADD: "+",
        z3.Z3_OP_SUB: "-",
        z3.Z3_OP_MUL: "*",
        z3.Z3_OP_DIV: "/",
        z3.Z3_OP_IDIV: "/",
        z3.Z3_OP_MOD: "%",
        z3.Z3_OP_LT: "<",
        z3.Z3_OP_LE: "<=",
        z3.Z3_OP_GT: ">",
        z3.Z3_OP_GE: ">=",
        z3.Z3_OP_EQ: "==",
        z3.Z3_OP_DISTINCT: "!=",
        z3.Z3_OP_AND: "&&",
        z3.Z3_OP_OR: "||",
        z3.Z3_OP_NOT: "!",
        z3.Z3_OP_IMPLIES: "-->",
    }
    if kind not in operators:
        raise ValueError(f"Unsupported Z3 operator {node.decl()}")
    base = _base(node.arg(0).sort())
    if len(children) == 1:
        return _apply_op(operators[kind], base, children[0])
    value = _apply_op(operators[kind], base, children[0], children[1])
    for child in children[2:]:
        value = _apply_op(operators[kind], base, value, child)
    return value


def solve_joint_z3(problem: SolverProblem, timeout_ms: int) -> JointCandidate:
    solver = z3.Solver()
    solver.set(timeout=max(1, timeout_ms))
    functions = {
        hole.symbol: z3.Function(
            str(hole.symbol), *[_sort(t) for _, t in hole.params] or [z3.IntSort()], _sort(hole.base)
        )
        for hole in problem.holes
    }
    for clause in problem.clauses:
        env = {str(name): function for name, function in functions.items()}
        variables = [z3.Const(str(name), _sort(base)) for name, base in clause.variables]
        env.update({str(name): variable for (name, _), variable in zip(clause.variables, variables)})
        implication = z3.Implies(translate_liq(clause.premise, env), translate_liq(clause.conclusion, env))
        solver.add(z3.ForAll(variables, implication) if variables else implication)
    result = solver.check()
    if result != z3.sat:
        detail = "unsatisfiable" if result == z3.unsat else f"unknown ({solver.reason_unknown()})"
        raise SynthesisNotSuccessful(f"Joint SMT: {detail}")
    model = solver.model()
    terms: list[Term] = []
    try:
        for hole in problem.holes:
            inputs = [z3.Const(str(name), _sort(base)) for name, base in hole.params]
            expression = _interpret(model, functions[hole.symbol], inputs or [z3.IntVal(0)])
            body = _decode(expression, dict(zip(inputs, [name for name, _ in hole.params])), model)
            terms.append(hole.wrap(body))
    except (ValueError, KeyError, z3.Z3Exception) as exc:
        raise SynthesisNotSuccessful(f"Joint SMT cannot translate its complete model: {exc}") from exc
    return JointCandidate(tuple(terms))
