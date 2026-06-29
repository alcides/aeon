from __future__ import annotations

import ast
import copy

from aeon.core.terms import Application, Literal, Term, Var
from aeon.core.types import t_bool, t_float, t_int, t_string
from aeon.utils.name import Name


class _SubstituteArg(ast.NodeTransformer):
    def __init__(self, param: str, arg: ast.expr):
        self.param = param
        self.arg = arg

    def visit_Name(self, node: ast.Name) -> ast.AST:
        if node.id == self.param and isinstance(node.ctx, ast.Load):
            return ast.copy_location(copy.deepcopy(self.arg), node)
        return node


def _native_var(name: Name) -> bool:
    return name.name == "native"


def native_code(fun: Term) -> str | None:
    match fun:
        case Application(Var(name), Literal(code, _)) if _native_var(name):
            return str(code)
        case _:
            return None


def native_term(code: str) -> Term:
    return Application(Var(Name("native")), Literal(code, t_string))


def literal_from_python(value: object) -> Literal:
    if isinstance(value, bool):
        return Literal(value, t_bool)
    if isinstance(value, int):
        return Literal(value, t_int)
    if isinstance(value, float):
        return Literal(value, t_float)
    if isinstance(value, str):
        return Literal(value, t_string)
    raise TypeError(f"unsupported native literal value: {value!r}")


def term_to_ast(t: Term) -> ast.expr | None:
    match t:
        case Literal(value, _):
            if isinstance(value, bool):
                return ast.Constant(value=value)
            if isinstance(value, int):
                return ast.Constant(value=value)
            if isinstance(value, float):
                return ast.Constant(value=value)
            if isinstance(value, str):
                return ast.Constant(value=value)
            if value is None:
                return ast.Constant(value=None)
            return None
        case Var(name):
            return ast.Name(id=name.name, ctx=ast.Load())
        case _:
            return None


def _has_load_name(node: ast.AST) -> bool:
    return any(isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) for n in ast.walk(node))


def _eval_constant_expr(node: ast.expr) -> object | None:
    if _has_load_name(node):
        return None
    try:
        return eval(compile(ast.Expression(node), "<native-opt>", "eval"), {"__builtins__": {}}, {})
    except Exception:
        return None


def ast_to_term(node: ast.expr) -> Term:
    if isinstance(node, ast.Constant):
        return literal_from_python(node.value)
    if isinstance(node, ast.Name):
        return Var(Name(node.id))
    if isinstance(node, ast.Lambda):
        return native_term(ast.unparse(node))
    folded = _eval_constant_expr(node)
    if folded is not None:
        return literal_from_python(folded)
    return native_term(ast.unparse(node))


def _parse_native_expr(code: str) -> ast.expr | None:
    try:
        return ast.parse(code, mode="eval").body
    except SyntaxError:
        return None


def _mentions_name(node: ast.AST, name: str) -> bool:
    return any(isinstance(n, ast.Name) and n.id == name for n in ast.walk(node))


def _beta_reduce_lambda(expr: ast.Lambda, arg: ast.expr) -> ast.expr:
    if len(expr.args.args) != 1 or expr.args.posonlyargs or expr.args.kwonlyargs or expr.args.kwarg:
        raise ValueError("only single-argument native lambdas are supported")
    param = expr.args.args[0].arg
    if not _mentions_name(expr.body, param):
        return expr.body
    body = _SubstituteArg(param, arg).visit(expr.body)
    assert isinstance(body, ast.expr)
    ast.fix_missing_locations(body)
    return body


def fold_native_expr(code: str) -> Term | None:
    expr = _parse_native_expr(code)
    if expr is None or isinstance(expr, (ast.Lambda, ast.Constant)):
        return None
    folded = _eval_constant_expr(expr)
    if folded is None:
        return None
    return literal_from_python(folded)


def beta_reduce_native(fun: Term, arg: Term) -> Term | None:
    code = native_code(fun)
    if code is None:
        return None
    expr = _parse_native_expr(code)
    if expr is None or not isinstance(expr, ast.Lambda):
        return None
    arg_expr = term_to_ast(arg)
    if arg_expr is None:
        return None
    try:
        reduced = _beta_reduce_lambda(expr, arg_expr)
    except ValueError:
        return None
    return ast_to_term(reduced)
