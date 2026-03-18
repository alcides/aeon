from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Dict, List

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
from aeon.llvm.core import LLVMLowerer, LLVMValidationError, ValidationStep, ValidationContext
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMTerm,
)
from aeon.llvm.utils import validate_type
from aeon.utils.name import Name


@dataclass(frozen=True)
class CPUValidationContext(ValidationContext):
    allowed_func_calls: set[Name] = field(default_factory=set)
    env_names: set[str] = field(default_factory=set)
    is_top_level: bool = True


class CPUTypeValidationStep(ValidationStep):
    def validate(self, t: Term, ctx: ValidationContext) -> None:
        match t:
            case Literal(_, ty):
                validate_type(ty)
            case Rec(_, var_type, var_value, body):
                validate_type(var_type)
                self.validate(var_value, ctx)
                self.validate(body, ctx)
            case Annotation(expr, ty) | TypeApplication(expr, ty):
                validate_type(ty)
                self.validate(expr, ctx)
            case Abstraction(_, body) | Let(_, _, body) | TypeAbstraction(_, _, body):
                self.validate(body, ctx)
                if isinstance(t, Let):
                    self.validate(t.var_value, ctx)
            case Application(f, arg):
                self.validate(f, ctx)
                self.validate(arg, ctx)
            case If(cond, then_t, else_t):
                self.validate(cond, ctx)
                self.validate(then_t, ctx)
                self.validate(else_t, ctx)
            case Var(_) | Hole(_):
                pass
            case _:
                pass


class CPUFunctionCallValidationStep(ValidationStep):
    def validate(self, t: Term, ctx: ValidationContext) -> None:
        assert isinstance(ctx, CPUValidationContext)
        match t:
            case Var(name):
                is_local = name.name in ctx.env_names
                is_anf = name.name.startswith("anf")
                is_allowed = name in ctx.allowed_func_calls

                if not (is_local or is_anf or is_allowed):
                    raise LLVMValidationError(
                        f"Function or variable {name.name} is not allowed in CPU LLVM functions. "
                        f"Only @llvm functions or built-in operators are permitted as global calls."
                    )
            case Rec(var_name, _, var_value, body):
                if ctx.is_top_level:
                    self.validate(var_value, replace(ctx, is_top_level=False))
                    self.validate(body, replace(ctx, is_top_level=True))
                else:
                    new_ctx = replace(ctx, env_names=ctx.env_names | {var_name.name}, is_top_level=False)
                    self.validate(var_value, new_ctx)
                    self.validate(body, new_ctx)
            case Let(var_name, var_value, body):
                if ctx.is_top_level:
                    self.validate(var_value, replace(ctx, is_top_level=False))
                    self.validate(body, replace(ctx, is_top_level=True))
                else:
                    self.validate(var_value, replace(ctx, is_top_level=False))
                    self.validate(body, replace(ctx, env_names=ctx.env_names | {var_name.name}, is_top_level=False))
            case Abstraction(var_name, body):
                self.validate(body, replace(ctx, env_names=ctx.env_names | {var_name.name}, is_top_level=False))
            case Application(f, arg):
                self.validate(f, replace(ctx, is_top_level=False))
                self.validate(arg, replace(ctx, is_top_level=False))
            case If(cond, then_t, else_t):
                self.validate(cond, replace(ctx, is_top_level=False))
                self.validate(then_t, replace(ctx, is_top_level=False))
                self.validate(else_t, replace(ctx, is_top_level=False))
            case Annotation(expr, _) | TypeApplication(expr, _) | TypeAbstraction(_, _, expr):
                self.validate(expr, ctx)
            case Literal(_, _) | Hole(_):
                pass
            case _:
                pass


class CPULLVMLowerer(LLVMLowerer):
    def get_validation_steps(self) -> List[ValidationStep]:
        return [CPUTypeValidationStep(), CPUFunctionCallValidationStep()]

    def lower(self, t: Term, type_env: Dict[Name, LLVMType] = None, env: Dict[Name, LLVMTerm] = None) -> LLVMTerm:
        pass
