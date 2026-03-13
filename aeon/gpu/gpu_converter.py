from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict
from aeon.core.terms import (
    Application,
    Abstraction,
    If,
    Let,
    Literal,
    Term,
    Var,
    TypeApplication,
    TypeAbstraction,
    Annotation,
    Rec,
)
from aeon.core.types import TypeConstructor, RefinedType, AbstractionType
from aeon.utils.name import Name


@dataclass(frozen=True)
class GType:
    name: str


GInt = GType("Int")
GFloat = GType("Float")
GBool = GType("Bool")
GChar = GType("Char")


@dataclass
class GTerm:
    type: GType


@dataclass
class GLiteral(GTerm):
    value: Any


@dataclass
class GVar(GTerm):
    name: Name


@dataclass
class GBinOp(GTerm):
    op: str
    left: GTerm
    right: GTerm


@dataclass
class GUnaryOp(GTerm):
    op: str
    arg: GTerm


@dataclass
class GIf(GTerm):
    cond: GTerm
    then_t: GTerm
    else_t: GTerm


@dataclass
class GLet(GTerm):
    var_name: Name
    var_value: GTerm
    body: GTerm


@dataclass
class GPartialBinOp(GTerm):
    op: str
    left: GTerm


BINARY_OPS = {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||"}
UNARY_OPS = {"!", "-"}


def from_type_to_gtype(ty) -> GType:
    match ty:
        case RefinedType(inner_type, _):
            return from_type_to_gtype(inner_type)
        case AbstractionType(_, _, return_type):
            return from_type_to_gtype(return_type)
        case TypeConstructor(name):
            match name.name:
                case "Int":
                    return GInt
                case "Float":
                    return GFloat
                case "Bool":
                    return GBool
                case "Char":
                    return GChar
                case _:
                    return GInt
        case _:
            return GInt


def convert_to_gpu_ast(t: Term, type_env: Dict[Name, GType], env: Dict[Name, GTerm] = None) -> GTerm:
    if env is None:
        env = {}
    match t:
        case Literal(value, ty):
            return GLiteral(type=from_type_to_gtype(ty), value=value)
        case Var(name):
            if name in env:
                return env[name]
            return GVar(type=type_env.get(name, GInt), name=name)
        case Application(fun_term, arg):
            f_ast = convert_to_gpu_ast(fun_term, type_env, env)
            arg_ast = convert_to_gpu_ast(arg, type_env, env)
            op = ""
            if isinstance(f_ast, GVar):
                op = f_ast.name.name
            if op in UNARY_OPS:
                ret_type = GBool if op == "!" else arg_ast.type
                return GUnaryOp(type=ret_type, op=op, arg=arg_ast)
            if op in BINARY_OPS:
                return GPartialBinOp(type=GInt, op=op, left=arg_ast)
            if isinstance(f_ast, GPartialBinOp) or (isinstance(f_ast, GUnaryOp) and f_ast.op in BINARY_OPS):
                op = f_ast.op
                left = f_ast.left if isinstance(f_ast, GPartialBinOp) else f_ast.arg
                ret_type = GBool if op in {"==", "!=", "<", "<=", ">", ">=", "&&", "||"} else left.type
                return GBinOp(type=ret_type, op=op, left=left, right=arg_ast)
            return arg_ast
        case If(cond, then_t, else_t):
            c_ast = convert_to_gpu_ast(cond, type_env, env)
            t_ast = convert_to_gpu_ast(then_t, type_env, env)
            e_ast = convert_to_gpu_ast(else_t, type_env, env)
            return GIf(type=t_ast.type, cond=c_ast, then_t=t_ast, else_t=e_ast)
        case Let(var_name, var_value, body):
            val_ast = convert_to_gpu_ast(var_value, type_env, env)
            new_env = env.copy()
            new_type_env = type_env.copy()
            new_env[var_name] = val_ast
            new_type_env[var_name] = val_ast.type
            res_body = convert_to_gpu_ast(body, new_type_env, new_env)
            return GLet(type=res_body.type, var_name=var_name, var_value=val_ast, body=res_body)
        case Rec(var_name, _, var_value, body):
            return convert_to_gpu_ast(Let(var_name, var_value, body), type_env, env)
        case Abstraction(_, body) | TypeAbstraction(_, _, body) | Annotation(body, _) | TypeApplication(body, _):
            return convert_to_gpu_ast(body, type_env, env)
        case _:
            raise Exception(f"Cannot convert term {t} to GPU AST")
