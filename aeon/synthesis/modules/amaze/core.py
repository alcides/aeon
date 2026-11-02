"""Typed Core conversion for closed, total, first-order Int/Bool expressions."""

from __future__ import annotations

import z3

from aeon.core.multiplicity import MOmega
from aeon.core.terms import Abstraction, Annotation, Application, If, Let, Literal, Term, TypeApplication, Var
from aeon.core.types import AbstractionType, RefinedType, Type, t_bool, t_int
from aeon.utils.name import Name
from .grammar import Expr, SIGNATURES, validate_expr

TYPES = {"Int": t_int, "Bool": t_bool}
POLY = {"+", "-", "*", "<", "<=", ">", ">=", "==", "!="}


def sort_of(ty: Type, *, refinements=False) -> str:
    if refinements and isinstance(ty, RefinedType):
        ty = ty.type
    for sort, value in TYPES.items():
        if ty == value:
            return sort
    raise ValueError(
        "supported sorts are monomorphic Int/Bool; abstract refinements and higher-order types are unsupported"
    )


def from_core(term: Term, variables: dict[Name, Expr]) -> Expr:
    if isinstance(term, Annotation):
        sort_of(term.type)
        return from_core(term.expr, variables)
    if isinstance(term, Literal):
        if not isinstance(term.value, (int, bool)):
            raise ValueError("non-scalar literal")
        expr = Expr("const", sort_of(term.type), value=term.value)
        validate_expr(expr, ())
        return expr
    if isinstance(term, Var) and term.name in variables:
        return variables[term.name]
    if isinstance(term, Let) and term.multiplicity is MOmega:
        value = from_core(term.var_value, variables)
        return from_core(term.body, variables | {term.var_name: value})
    if isinstance(term, If):
        branches = tuple(from_core(t, variables) for t in (term.cond, term.then, term.otherwise))
        return Expr("ifI" if branches[1].sort == "Int" else "ifB", branches[1].sort, branches)
    args: list[Term] = []
    head = term
    while isinstance(head, Application):
        args.insert(0, head.arg)
        head = head.fun
    type_args = []
    while isinstance(head, TypeApplication):
        type_args.append(sort_of(head.type))
        head = head.body
    if not isinstance(head, Var) or head.name.id != 0:
        raise ValueError("native/effectful call, recursion, helper dependency or unsupported Core term")
    op = head.name.name
    expressions = tuple(from_core(a, variables) for a in args)
    if op in ("==", "!=") and expressions:
        op += "I" if expressions[0].sort == "Int" else "B"
    if op not in SIGNATURES:
        raise ValueError("primitive outside the fixed pure grammar")
    sorts, out = SIGNATURES[op]
    if tuple(e.sort for e in expressions) != sorts or any(t != sorts[0] for t in type_args):
        raise ValueError("primitive application type mismatch")
    return Expr(op, out, expressions)


def to_core(expr: Expr, variables: tuple[Name, ...]) -> Term:
    if expr.op == "var":
        return Var(variables[int(expr.value)])
    if expr.op == "const":
        return Literal(expr.value, TYPES[expr.sort])
    args = [to_core(c, variables) for c in expr.children]
    if expr.op in ("ifI", "ifB"):
        return If(args[0], args[1], args[2])
    op = expr.op[:-1] if expr.op in ("==I", "==B", "!=I", "!=B") else expr.op
    term: Term = Var(Name(op, 0))
    if op in POLY:
        term = TypeApplication(term, TYPES[expr.children[0].sort])
    for arg in args:
        term = Application(term, arg)
    return term


def unwrap(body: Term, ty: Type):
    variables, sorts = [], []
    while isinstance(ty, AbstractionType):
        if ty.multiplicity is not MOmega or not isinstance(body, Abstraction):
            raise ValueError("linear/erased/polymorphic multiplicities are unsupported")
        sorts.append(sort_of(ty.var_type))
        variables.append(body.var_name)
        body, ty = body.body, ty.type
    result = sort_of(ty)
    expr = from_core(body, {n: Expr("var", s, value=i) for i, (n, s) in enumerate(zip(variables, sorts))})
    if validate_expr(expr, tuple(sorts)) != result:
        raise ValueError("reference signature mismatch")
    return tuple(variables), tuple(sorts), expr


def wrap(expr: Expr, variables: tuple[Name, ...]) -> Term:
    result = to_core(expr, variables)
    for name in reversed(variables):
        result = Abstraction(name, result)
    return result


def equivalent(left: Expr, right: Expr, sorts: tuple[str, ...], timeout_ms=200) -> str:
    context = z3.Context()
    variables = [z3.Int(f"x{i}", context) if s == "Int" else z3.Bool(f"x{i}", context) for i, s in enumerate(sorts)]

    def convert(e):
        if e.op == "var":
            return variables[int(e.value)]
        if e.op == "const":
            return z3.IntVal(e.value, context) if e.sort == "Int" else z3.BoolVal(e.value, context)
        args = [convert(c) for c in e.children]
        a = args[0]
        b = args[1] if len(args) > 1 else None
        ops = {
            "+": lambda: a + b,
            "-": lambda: a - b,
            "*": lambda: a * b,
            "<": lambda: a < b,
            "<=": lambda: a <= b,
            ">": lambda: a > b,
            ">=": lambda: a >= b,
            "==I": lambda: a == b,
            "==B": lambda: a == b,
            "!=I": lambda: a != b,
            "!=B": lambda: a != b,
            "&&": lambda: z3.And(a, b),
            "||": lambda: z3.Or(a, b),
            "!": lambda: z3.Not(a),
            "-->": lambda: z3.Implies(a, b),
            "ifI": lambda: z3.If(*args),
            "ifB": lambda: z3.If(*args),
        }
        return ops[e.op]()

    solver = z3.Solver(ctx=context)
    solver.set(timeout=max(1, timeout_ms))
    solver.add(convert(left) != convert(right))
    result = solver.check()
    return "equivalent" if result == z3.unsat else "different" if result == z3.sat else "unknown"
