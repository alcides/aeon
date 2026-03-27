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
    LLVMFloatType,
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
                arguments = [arg]
                base_function = fun
                while isinstance(base_function, Application):
                    arguments.append(base_function.arg)
                    base_function = base_function.fun

                for a in arguments:
                    self.validate(a, replace(ctx, is_top_level=False))
                self.validate(base_function, replace(ctx, is_top_level=False))

            case Let(var_name, var_value, body):
                llvm_var_type: LLVMType = LLVMInt
                if isinstance(var_value, Annotation):
                    llvm_var_type = from_type_to_llvm_type(var_value.type)
                elif isinstance(var_value, Rec):
                    llvm_var_type = from_type_to_llvm_type(var_value.var_type)
                elif isinstance(var_value, Var) and var_value.name.name in BINARY_OPS:
                    llvm_var_type = get_builtin_op_type(var_value.name.name)

                new_ctx = replace(ctx, type_env=ctx.type_env | {var_name: llvm_var_type}, is_top_level=False)
                self.validate(var_value, replace(ctx, is_top_level=False))
                self.validate(body, new_ctx)

            case Rec(var_name, var_ty, var_value, body):
                llvm_ty = from_type_to_llvm_type(var_ty)
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

    def _uncurry_application(self, application: Application) -> tuple[Term, List[Term]]:
        arguments = [application.arg]
        base_function = application.fun
        while isinstance(base_function, Application):
            arguments.append(base_function.arg)
            base_function = base_function.fun
        arguments.reverse()
        return base_function, arguments

    def _get_operator_type(self, op_name: str, expected_type: LLVMType | None) -> LLVMFunctionType:
        is_float = False
        if expected_type:
            if isinstance(expected_type, LLVMFunctionType):
                is_float = any(isinstance(ty, LLVMFloatType) for ty in expected_type.arg_types)
            elif isinstance(expected_type, LLVMFloatType):
                is_float = True
        return get_builtin_op_type(op_name, is_float)

    def _is_inlinable_anf(self, var_name: Name, llvm_value: LLVMTerm) -> bool:
        if not var_name.name.startswith("anf"):
            return False
        is_partial_call = isinstance(llvm_value, LLVMCall) and isinstance(llvm_value.type, LLVMFunctionType)
        is_operator = isinstance(llvm_value, LLVMVar) and (
            llvm_value.name.name in BINARY_OPS or llvm_value.name.name in UNARY_OPS
        )
        return is_partial_call or is_operator

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
                    llvm_type = self._get_operator_type(name.name, expected_type)
                    return LLVMVar(llvm_type, name)
                elif name in env:
                    return env[name]
                else:
                    llvm_type = type_env.get(name) or LLVMInt
                    return LLVMVar(llvm_type, name)

            case Annotation(expr, type) | TypeApplication(expr, type):
                llvm_type = from_type_to_llvm_type(type)
                return self.lower(expr, llvm_type, type_env, env)

            case Application(_, _):
                base_function, application_args = self._uncurry_application(t)
                lowered_base_function = self.lower(base_function, None, type_env, env)

                is_partial_application = isinstance(lowered_base_function, LLVMCall) and isinstance(
                    lowered_base_function.type, LLVMFunctionType
                )
                if is_partial_application:
                    function_target = lowered_base_function.target
                    previously_applied_args = lowered_base_function.args
                    full_function_type = function_target.type
                else:
                    function_target = lowered_base_function
                    previously_applied_args = []
                    full_function_type = lowered_base_function.type

                all_lowered_args = previously_applied_args.copy()
                for arg in application_args:
                    arg_index = len(all_lowered_args)
                    expected_arg_type = full_function_type.arg_types[arg_index]
                    all_lowered_args.append(self.lower(arg, expected_arg_type, type_env, env))

                is_still_partial = len(all_lowered_args) < len(full_function_type.arg_types)
                if is_still_partial:
                    unapplied_arg_types = full_function_type.arg_types[len(all_lowered_args) :]
                    partial_return_type = LLVMFunctionType(
                        arg_types=unapplied_arg_types, return_type=full_function_type.return_type
                    )
                    return LLVMCall(type=partial_return_type, target=function_target, args=all_lowered_args)
                else:
                    return LLVMCall(type=full_function_type.return_type, target=function_target, args=all_lowered_args)

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

                new_env = env.copy()

                if self._is_inlinable_anf(var_name, llvm_value):
                    new_env[var_name] = llvm_value
                    return self.lower(body, expected_type, new_type_env, new_env)

                new_env[var_name] = LLVMVar(llvm_value.type, var_name)
                llvm_body = self.lower(body, expected_type, new_type_env, new_env)
                return LLVMLet(type=llvm_body.type, var_name=var_name, var_value=llvm_value, body=llvm_body)

            case Rec(var_name, var_type, var_value, body):
                llvm_func_type = from_type_to_llvm_type(var_type)

                new_type_env = type_env.copy()
                new_type_env[var_name] = llvm_func_type

                new_env = env.copy()
                new_env[var_name] = LLVMVar(llvm_func_type, var_name)

                llvm_func_value = self.lower(var_value, llvm_func_type, new_type_env, new_env)
                llvm_body = self.lower(body, expected_type, new_type_env, new_env)

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
