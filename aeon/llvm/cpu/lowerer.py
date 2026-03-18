from __future__ import annotations

from typing import Dict

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
    Hole,
)
from aeon.llvm.llvm_ast import LLVMType, LLVMTerm
from aeon.utils.name import Name

from aeon.llvm.core import LLVMLowerer, LLVMValidationError

from aeon.llvm.utils import validate_type, UNARY_OPS, BINARY_OPS


class CPULLVMLowerer(LLVMLowerer):
    def validate(
        self,
        t: Term,
        rec_scope: set[Name] = None,
        env_names: set[str] = None,
        allowed_func_calls: set[Name] = None,
        is_top_level: bool = True,
    ):
        if rec_scope is None:
            rec_scope = set()
        if env_names is None:
            env_names = set()
        if allowed_func_calls is None:
            allowed_func_calls = set()

        match t:
            case Literal(_, ty):
                validate_type(ty)
            case Var(name):
                is_op = name.name in BINARY_OPS or name.name in UNARY_OPS
                is_bound = name in rec_scope or name.name in env_names
                is_anf = name.name.startswith("anf")
                is_allowed_global = name in allowed_func_calls

                if not (is_op or is_bound or is_anf or is_allowed_global):
                    raise LLVMValidationError(
                        f"{name.name} is not in scope or not allowed in LLVM functions."
                        f"LLVM functions can only call other @llvm functions or built-in operators."
                    )

            case Rec(var_name, var_type, var_value, body):
                validate_type(var_type)
                if is_top_level:
                    self.validate(var_value, rec_scope | {var_name}, env_names, allowed_func_calls, is_top_level=False)
                    self.validate(body, rec_scope, env_names, allowed_func_calls, is_top_level=True)
                else:
                    self.validate(
                        var_value,
                        rec_scope | {var_name},
                        env_names | {var_name.name},
                        allowed_func_calls,
                        is_top_level=False,
                    )
                    self.validate(body, rec_scope, env_names | {var_name.name}, allowed_func_calls, is_top_level=False)

            case Application(f, arg):
                self.validate(f, rec_scope, env_names, allowed_func_calls, is_top_level=False)
                self.validate(arg, rec_scope, env_names, allowed_func_calls, is_top_level=False)

            case Let(var_name, val, body):
                if is_top_level:
                    self.validate(val, rec_scope, env_names, allowed_func_calls, is_top_level=False)
                    self.validate(body, rec_scope, env_names, allowed_func_calls, is_top_level=True)
                else:
                    self.validate(val, rec_scope, env_names, allowed_func_calls, is_top_level=False)
                    self.validate(body, rec_scope, env_names | {var_name.name}, allowed_func_calls, is_top_level=False)

            case Abstraction(var_name, body):
                self.validate(body, rec_scope, env_names | {var_name.name}, allowed_func_calls, is_top_level=False)

            case If(cond, then_t, else_t):
                for branch in [cond, then_t, else_t]:
                    self.validate(branch, rec_scope, env_names, allowed_func_calls, is_top_level=False)

            case Annotation(expr, ty) | TypeApplication(expr, ty):
                validate_type(ty)
                self.validate(expr, rec_scope, env_names, allowed_func_calls, is_top_level)

            case TypeAbstraction(_, _, body):
                self.validate(body, rec_scope, env_names, allowed_func_calls, is_top_level)

            case Hole(_):
                pass

            case _:
                raise LLVMValidationError(f"{type(t).__name__} not supported in CPU LLVM backend.")

    def lower(self, t: Term, type_env: Dict[Name, LLVMType] = None, env: Dict[Name, LLVMTerm] = None) -> LLVMTerm:
        pass
