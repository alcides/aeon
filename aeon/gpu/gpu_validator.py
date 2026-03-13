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
from aeon.utils.name import Name


def validate_gpu_subset(t: Term, used_functions: set[Name] = None):
    if used_functions is None:
        used_functions = set()
    match t:
        case Literal(_, _):
            pass
        case Rec(var_name, _, var_value, body):
            used_functions = used_functions | {var_name}
            validate_gpu_subset(var_value, used_functions)
            validate_gpu_subset(body, used_functions)
        case Application(f, arg):
            validate_gpu_subset(f, used_functions)
            validate_gpu_subset(arg, used_functions)
        case If(cond, then_t, else_t):
            validate_gpu_subset(cond, used_functions)
            validate_gpu_subset(then_t, used_functions)
            validate_gpu_subset(else_t, used_functions)
        case Let(_, val, body):
            validate_gpu_subset(val, used_functions)
            validate_gpu_subset(body, used_functions)
        case Abstraction(_, body) | TypeAbstraction(_, _, body):
            validate_gpu_subset(body, used_functions)
        case Annotation(expr, _) | TypeApplication(expr, _):
            validate_gpu_subset(expr, used_functions)
        case Var(name):
            if name in used_functions:
                raise Exception("GPU Kernels do not support recursion")
        case _:
            raise Exception(f"{type(t).__name__} is not supported in the GPU subset.")
