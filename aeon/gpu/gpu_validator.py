from __future__ import annotations

from aeon.core.terms import (
    Abstraction,
    Application,
    If,
    Let,
    Literal,
    Rec,
    Term,
    Var,
    TypeApplication,
    TypeAbstraction,
    Annotation,
)
from aeon.core.types import TypeConstructor, RefinedType, AbstractionType
from aeon.utils.name import Name

SUPPORTED_TYPES = {"Int", "Float", "Bool", "Char"}
BINARY_OPS = {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||"}
UNARY_OPS = {"!", "-"}


def validate_ops(op: str):
    if op.startswith("anf"):
        return
    if op not in BINARY_OPS and op not in UNARY_OPS:
        raise Exception(f"GPU Kernels do not support operation {op}")


def validate_type(ty):
    match ty:
        case RefinedType(inner, _):
            validate_type(inner)
        case AbstractionType(var_ty, _, ret_ty):
            validate_type(var_ty)
            validate_type(ret_ty)
        case TypeConstructor(name):
            if name.name not in SUPPORTED_TYPES:
                raise Exception(f"GPU Kernels do not support type: {name.name}")
        case _:
            pass


def validate_gpu_subset(
    t: Term,
    rec_scope: set[Name] = None,
):
    if rec_scope is None:
        rec_scope = set()

    match t:
        case Literal(_, ty):
            validate_type(ty)
        case Var(name):
            if name in rec_scope:
                raise Exception(f"Recursion detected in GPU kernel: {name.name}")
        case Rec(var_name, var_type, var_value, body):
            validate_type(var_type)
            validate_gpu_subset(var_value, rec_scope | {var_name})
            validate_gpu_subset(body, rec_scope)
        case Application(f, arg):
            if isinstance(f, Var):
                validate_ops(f.name.name)
            validate_gpu_subset(f, rec_scope)
            validate_gpu_subset(arg, rec_scope)
        case Let(_, val, body):
            validate_gpu_subset(val, rec_scope)
            validate_gpu_subset(body, rec_scope)
        case Abstraction(var_name, body) | TypeAbstraction(var_name, _, body):
            validate_gpu_subset(body, rec_scope)
        case If(cond, then_t, else_t):
            for branch in [cond, then_t, else_t]:
                validate_gpu_subset(branch, rec_scope)
        case Annotation(expr, ty) | TypeApplication(expr, ty):
            validate_type(ty)
            validate_gpu_subset(expr, rec_scope)
        case _:
            raise Exception(f"{type(t).__name__} is not supported in GPU subset.")
