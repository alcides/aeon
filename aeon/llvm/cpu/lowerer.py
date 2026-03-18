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
from aeon.llvm.core import LLVMLowerer, LLVMValidationError, ValidationStep, ValidationContext, LLVMBackendError
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMTerm,
    LLVMLiteral,
    LLVMInt,
    LLVMVar,
    LLVMIf,
    LLVMCall,
    LLVMFunctionType,
    LLVMLet,
    LLVMAbstraction,
)
from aeon.llvm.utils import validate_type, from_type_to_llvm_type, UNARY_OPS, BINARY_OPS, get_builtin_op_type
from aeon.utils.name import Name


class LLVMLoweringError(LLVMBackendError):
    pass


@dataclass(frozen=True)
class CPUValidationContext(ValidationContext):
    allowed_func_calls: set[Name] = field(default_factory=set)
    type_env: Dict[Name, LLVMType] = field(default_factory=dict)
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
            case Hole(name):
                raise LLVMValidationError(f"Unresolved hole {name}")
            case Var(_) | _:
                pass


class CPUFunctionCallValidationStep(ValidationStep):
    def validate(self, t: Term, ctx: ValidationContext) -> None:
        assert isinstance(ctx, CPUValidationContext)
        match t:
            case Var(name):
                is_local = name.name in ctx.env_names
                is_op = name.name in BINARY_OPS or name.name in UNARY_OPS
                is_anf = name.name.startswith("anf")
                is_allowed = name in ctx.allowed_func_calls

                if not (is_local or is_op or is_anf or is_allowed):
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


class CPUFullApplicationValidationStep(ValidationStep):
    def validate(self, t: Term, ctx: ValidationContext) -> None:
        assert isinstance(ctx, CPUValidationContext)
        match t:
            case Application(fun, arg):
                args = [arg]
                current_fun = fun
                while isinstance(current_fun, Application):
                    args.append(current_fun.arg)
                    current_fun = current_fun.fun

                target_type = None
                if isinstance(current_fun, Var):
                    name = current_fun.name.name
                    if name in BINARY_OPS or name in UNARY_OPS:
                        target_type = get_builtin_op_type(name)
                    else:
                        target_type = ctx.type_env.get(current_fun.name)
                elif isinstance(current_fun, Annotation):
                    target_type = from_type_to_llvm_type(current_fun.type)

                if isinstance(target_type, LLVMFunctionType):
                    if len(args) != len(target_type.arg_types):
                        raise LLVMValidationError(
                            f"Function application of {current_fun} is not fully applied. "
                            f"Expected {len(target_type.arg_types)} arguments, got {len(args)}. "
                            f"LLVM backend requires full application."
                        )

                for a in args:
                    self.validate(a, replace(ctx, is_top_level=False))
                self.validate(current_fun, replace(ctx, is_top_level=False))

            case Let(var_name, var_value, body):
                var_type = LLVMInt
                if isinstance(var_value, Annotation):
                    var_type = from_type_to_llvm_type(var_value.type)
                elif isinstance(var_value, Rec):
                    var_type = from_type_to_llvm_type(var_value.var_type)

                new_ctx = replace(ctx, type_env=ctx.type_env | {var_name: var_type}, is_top_level=False)
                self.validate(var_value, replace(ctx, is_top_level=False))
                self.validate(body, new_ctx)

            case Rec(var_name, var_type, var_value, body):
                llvm_ty = from_type_to_llvm_type(var_type)
                new_ctx = replace(ctx, type_env=ctx.type_env | {var_name: llvm_ty}, is_top_level=False)
                self.validate(var_value, new_ctx)
                self.validate(body, new_ctx)

            case Abstraction(var_name, body):
                self.validate(body, replace(ctx, is_top_level=False))

            case If(cond, then_t, else_t):
                self.validate(cond, replace(ctx, is_top_level=False))
                self.validate(then_t, replace(ctx, is_top_level=False))
                self.validate(else_t, replace(ctx, is_top_level=False))

            case Annotation(expr, _) | TypeApplication(expr, _) | TypeAbstraction(_, _, expr):
                self.validate(expr, ctx)

            case Var(_) | Literal(_, _) | Hole(_):
                pass
            case _:
                pass


class CPULLVMLowerer(LLVMLowerer):
    def get_validation_steps(self) -> List[ValidationStep]:
        return [CPUTypeValidationStep(), CPUFunctionCallValidationStep(), CPUFullApplicationValidationStep()]

    def lower(
        self,
        t: Term,
        expected_type: LLVMType = None,
        type_env: Dict[Name, LLVMType] = None,
        env: Dict[Name, LLVMTerm] = None,
    ) -> LLVMTerm:
        if type_env is None:
            type_env = {}
        if env is None:
            env = {}

        match t:
            case Literal(value, type):
                llvm_type = from_type_to_llvm_type(type)
                return LLVMLiteral(llvm_type, value)

            case Var(name):
                if name.name in BINARY_OPS or name.name in UNARY_OPS:
                    llvm_type = get_builtin_op_type(name.name)
                else:
                    llvm_type = type_env.get(name) or LLVMInt
                return LLVMVar(llvm_type, name)

            case Annotation(expr, type) | TypeApplication(expr, type):
                llvm_type = from_type_to_llvm_type(type)
                return self.lower(expr, llvm_type, type_env, env)

            case Application(fun, arg):
                args = [arg]  # uncurry
                current_fun = fun
                while isinstance(current_fun, Application):
                    args.append(current_fun.arg)
                    current_fun = current_fun.fun
                args.reverse()

                llvm_fun = self.lower(current_fun, None, type_env, env)

                assert isinstance(llvm_fun.type, LLVMFunctionType)
                assert len(args) == len(llvm_fun.type.arg_types)

                llvm_args = []
                for i, a in enumerate(args):
                    expected_arg_ty = llvm_fun.type.arg_types[i]
                    llvm_args.append(self.lower(a, expected_arg_ty, type_env, env))

                return LLVMCall(type=llvm_fun.type.return_type, target=llvm_fun, args=llvm_args)

            case Abstraction(var_name, body):
                names = [var_name]
                current_body = body
                while isinstance(current_body, Abstraction):
                    names.append(current_body.var_name)
                    current_body = current_body.body

                assert expected_type is not None and isinstance(expected_type, LLVMFunctionType)
                assert len(names) == len(expected_type.arg_types)

                arg_types = expected_type.arg_types
                res_type = expected_type.return_type

                new_type_env = type_env.copy()
                for n, ty in zip(names, arg_types):
                    new_type_env[n] = ty

                llvm_body = self.lower(current_body, res_type, new_type_env, env)
                return LLVMAbstraction(type=expected_type, arg_names=names, arg_types=arg_types, body=llvm_body)

            case Let(var_name, var_value, body):
                llvm_value = self.lower(var_value, None, type_env, env)

                new_type_env = type_env.copy()
                new_type_env[var_name] = llvm_value.type

                llvm_body = self.lower(body, expected_type, new_type_env, env)
                return LLVMLet(type=llvm_body.type, var_name=var_name, var_value=llvm_value, body=llvm_body)

            case Rec(var_name, var_type, var_value, body):
                llvm_func_type = from_type_to_llvm_type(var_type)

                new_type_env = type_env.copy()
                new_type_env[var_name] = llvm_func_type

                llvm_func_value = self.lower(var_value, llvm_func_type, new_type_env, env)
                llvm_body = self.lower(body, expected_type, new_type_env, env)

                return LLVMLet(type=llvm_body.type, var_name=var_name, var_value=llvm_func_value, body=llvm_body)

            case If(cond, then, otherwise):
                llvm_cond = self.lower(cond, None, type_env, env)
                llvm_then = self.lower(then, expected_type, type_env, env)
                llvm_otherwise = self.lower(otherwise, expected_type, type_env, env)
                return LLVMIf(llvm_then.type, llvm_cond, llvm_then, llvm_otherwise)

            case TypeAbstraction(_, _, body):
                return self.lower(body, expected_type, type_env, env)

            case _:
                raise LLVMLoweringError(f"Could not lower term {t}")
