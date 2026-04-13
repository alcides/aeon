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
from aeon.core.types import Type
from aeon.llvm.core import LLVMLowerer, LLVMValidationError, ValidationStep, ValidationContext, LLVMBackendError
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMTerm,
    LLVMLiteral,
    LLVMInt,
    LLVMDouble,
    LLVMFloatType,
    LLVMDoubleType,
    LLVMBool,
    LLVMVar,
    LLVMIf,
    LLVMCall,
    LLVMFunctionType,
    LLVMLet,
    LLVMFunction,
    LLVMGetElementPtr,
    LLVMLoad,
    LLVMStore,
    LLVMPointerType,
    LLVMVoid,
    LLVMVoidType,
    LLVMCharType,
    LLVMVectorMap,
    LLVMVectorReduce,
    LLVMVectorIMap,
    LLVMVectorFilter,
    LLVMVectorZipWith,
    LLVMVectorCount,
    VECTOR_OPERATIONS,
    LLVMCast,
)
from aeon.llvm.utils import (
    validate_type,
    to_llvm_type,
    UNARY_OPS,
    BINARY_OPS,
    get_builtin_op_type,
    sanitize_name,
)
from aeon.utils.name import Name


class LLVMLoweringError(LLVMBackendError):
    pass


_generic_ptr = LLVMPointerType(LLVMCharType())
_func_i_i = LLVMFunctionType([LLVMInt], LLVMInt)
_func_ii_i = LLVMFunctionType([LLVMInt, LLVMInt], LLVMInt)
_func_i_b = LLVMFunctionType([LLVMInt], LLVMBool)

BUILTIN_FUNCTION_TYPES: Dict[str, LLVMFunctionType] = {
    "malloc": LLVMFunctionType([LLVMInt], _generic_ptr),
    "free": LLVMFunctionType([_generic_ptr], LLVMVoid),
    "printf": LLVMFunctionType([_generic_ptr], LLVMInt),
    "Math_pow": LLVMFunctionType([LLVMInt, LLVMInt], LLVMInt),
    "Math_powf": LLVMFunctionType([LLVMDouble, LLVMDouble], LLVMDouble),
    "Math_sqrt": LLVMFunctionType([LLVMDouble], LLVMDouble),
    "Math_sqrtf": LLVMFunctionType([LLVMDouble], LLVMDouble),
    "Math_sin": LLVMFunctionType([LLVMDouble, LLVMDouble], LLVMDouble),
    "Math_cos": LLVMFunctionType([LLVMDouble, LLVMDouble], LLVMDouble),
    "Math_exp": LLVMFunctionType([LLVMDouble], LLVMDouble),
    "Math_log": LLVMFunctionType([LLVMDouble], LLVMDouble),
    "Vector_new": LLVMFunctionType([], _generic_ptr),
    "Vector_append": LLVMFunctionType([_generic_ptr, LLVMInt], _generic_ptr),
    "Vector_get": LLVMFunctionType([_generic_ptr, LLVMInt], LLVMInt),
    "Vector_set": LLVMFunctionType([_generic_ptr, LLVMInt, LLVMInt], _generic_ptr),
    "Vector_map": LLVMFunctionType([LLVMPointerType(_func_i_i), _generic_ptr, LLVMInt], _generic_ptr),
    "Vector_reduce": LLVMFunctionType([LLVMPointerType(_func_ii_i), LLVMInt, _generic_ptr, LLVMInt], LLVMInt),
    "Vector_imap": LLVMFunctionType([LLVMPointerType(_func_ii_i), _generic_ptr, LLVMInt], _generic_ptr),
    "Vector_filter": LLVMFunctionType([LLVMPointerType(_func_i_b), _generic_ptr, LLVMInt], _generic_ptr),
    "Vector_zipWith": LLVMFunctionType(
        [LLVMPointerType(_func_ii_i), _generic_ptr, _generic_ptr, LLVMInt], _generic_ptr
    ),
    "Vector_count": LLVMFunctionType([LLVMPointerType(_func_i_b), _generic_ptr, LLVMInt], LLVMInt),
}

POLYMORPHIC_FUNCTIONS: set[str] = {
    "Math_pow",
    "Math_powf",
    "Math_exp",
    "Math_sqrt",
    "Math_sqrtf",
    "Math_sin",
    "Math_cos",
    "Math_log",
    "Vector_get",
    "Vector_set",
    "Vector_new",
    "Vector_map",
    "Vector_reduce",
    "Vector_imap",
    "Vector_filter",
    "Vector_zipWith",
    "Vector_count",
}


@dataclass(frozen=True)
class CPUValidationContext(ValidationContext):
    allowed_func_calls: set[Name] = field(default_factory=set)
    type_env: Dict[Name, LLVMType] = field(default_factory=dict)
    env_names: set[str] = field(default_factory=set)
    is_top_level: bool = True
    strict: bool = False
    in_vector_op: bool = False


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
            case Abstraction(_, body) | TypeAbstraction(_, _, body):
                self.validate(body, ctx)
            case Let(_, var_value, body):
                self.validate(var_value, ctx)
                self.validate(body, ctx)
            case Application(f, arg):
                self.validate(f, ctx)
                self.validate(arg, ctx)
            case If(cond, then_t, else_t):
                for sub in (cond, then_t, else_t):
                    self.validate(sub, ctx)
            case Hole(_):
                pass
            case Var(_):
                pass
            case _:
                raise LLVMValidationError(f"Unsupported term in LLVM backend: {type(t)}")


class CPUFunctionCallValidationStep(ValidationStep):
    def validate(self, t: Term, ctx: ValidationContext) -> None:
        assert isinstance(ctx, CPUValidationContext)
        match t:
            case Var(name) if not name.name.startswith("anf"):
                self._validate_var_call(name, ctx)
            case Application(fun, arg):
                self.validate(fun, ctx)
                self.validate(arg, ctx)
            case Let(var_name, var_value, body):
                self._validate_let(var_name, var_value, body, ctx)
            case Rec(var_name, _, var_value, body):
                self._validate_let(var_name, var_value, body, ctx)
            case Annotation(expr, _) | TypeApplication(expr, _) | TypeAbstraction(_, _, expr) | Abstraction(_, expr):
                self.validate(expr, ctx)
            case If(cond, then_t, else_t):
                for sub in (cond, then_t, else_t):
                    self.validate(sub, ctx)
            case _:
                pass

    def _validate_var_call(self, name: Name, ctx: CPUValidationContext) -> None:
        str_name = sanitize_name(name)
        is_builtin = name.name in BINARY_OPS or name.name in UNARY_OPS or name.name in BUILTIN_FUNCTION_TYPES
        is_allowed = name in ctx.allowed_func_calls or str_name in ctx.env_names
        if not (is_builtin or is_allowed or name.name == "native" or name.name == "Math_PI"):
            if ctx.strict:
                raise LLVMValidationError(f"Function {name.name} is not allowed in this LLVM context")

    def _validate_let(self, var_name: Name, var_value: Term, body: Term, ctx: CPUValidationContext) -> None:
        if ctx.is_top_level:
            self.validate(var_value, replace(ctx, is_top_level=False))
            self.validate(body, replace(ctx, is_top_level=True))
        else:
            self.validate(var_value, replace(ctx, is_top_level=False))
            self.validate(body, replace(ctx, env_names=ctx.env_names | {sanitize_name(var_name)}, is_top_level=False))


class CPUFullApplicationValidationStep(ValidationStep):
    def validate(self, t: Term, ctx: ValidationContext) -> None:
        assert isinstance(ctx, CPUValidationContext)
        no_top = replace(ctx, is_top_level=False)
        match t:
            case Application(fun, arg):
                arguments = [arg]
                base = fun
                while isinstance(base, Application):
                    arguments.append(base.arg)
                    base = base.fun
                for a in arguments:
                    self.validate(a, no_top)
                self.validate(base, no_top)
            case Let(var_name, var_value, body):
                llvm_var_type = self._infer_let_type(var_value)
                self.validate(var_value, no_top)
                self.validate(body, replace(ctx, type_env=ctx.type_env | {var_name: llvm_var_type}, is_top_level=False))
            case Rec(var_name, var_ty, var_value, body):
                llvm_ty = to_llvm_type(var_ty)
                new_ctx = replace(ctx, type_env=ctx.type_env | {var_name: llvm_ty}, is_top_level=False)
                self.validate(var_value, new_ctx)
                self.validate(body, new_ctx)
            case Abstraction(_, body) | Annotation(body, _) | TypeApplication(body, _) | TypeAbstraction(_, _, body):
                self.validate(body, no_top)
            case If(cond, then_t, else_t):
                for sub in (cond, then_t, else_t):
                    self.validate(sub, no_top)
            case _:
                pass

    @staticmethod
    def _infer_let_type(var_value: Term) -> LLVMType:
        if isinstance(var_value, Annotation):
            return to_llvm_type(var_value.type)
        if isinstance(var_value, Rec):
            return to_llvm_type(var_value.var_type)
        if isinstance(var_value, Var) and var_value.name.name in BINARY_OPS:
            return get_builtin_op_type(var_value.name.name)
        return LLVMInt


class CPULLVMLowerer(LLVMLowerer):
    def get_validation_steps(self) -> List[ValidationStep]:
        return [CPUTypeValidationStep(), CPUFunctionCallValidationStep(), CPUFullApplicationValidationStep()]

    def lower(
        self,
        term: Term,
        expected_type: LLVMType | None = None,
        type_env: Dict[Name, LLVMType] | None = None,
        env: Dict[Name, LLVMTerm] | None = None,
        allowed_func_calls: set[Name] | None = None,
        strict: bool = False,
        in_vector_op: bool = False,
    ) -> LLVMTerm:
        type_env = type_env or {}
        env = env or {}
        allowed_func_calls = allowed_func_calls or set()

        validation_ctx = CPUValidationContext(
            allowed_func_calls=allowed_func_calls,
            type_env=type_env,
            env_names={sanitize_name(n) for n in env.keys()},
            is_top_level=True,
            strict=strict,
            in_vector_op=in_vector_op,
        )
        for step in self.get_validation_steps():
            step.validate(term, validation_ctx)

        return self._lower_term(term, expected_type, type_env, env, allowed_func_calls, in_vector_op=in_vector_op)

    def get_signature(self, llvm_type: LLVMType) -> tuple[List[LLVMType], LLVMType]:
        arg_types: list[LLVMType] = []
        curr = llvm_type
        while True:
            if isinstance(curr, LLVMFunctionType):
                arg_types.extend(curr.arg_types)
                curr = curr.return_type
            elif isinstance(curr, LLVMPointerType) and isinstance(curr.element_type, LLVMFunctionType):
                curr = curr.element_type
            else:
                break
        return arg_types, curr

    def _get_vector_base_type(self, vector_type: LLVMType) -> LLVMType:
        if isinstance(vector_type, LLVMPointerType):
            element = vector_type.element_type
            if not isinstance(element, (LLVMCharType, LLVMPointerType)):
                return element
            if isinstance(element, LLVMCharType):
                return LLVMInt
        return LLVMInt

    def _get_operator_type(self, op: str, expected: LLVMType | None) -> LLVMFunctionType:
        is_float = False
        if expected:
            if isinstance(expected, LLVMFunctionType):
                is_float = any(isinstance(ty, (LLVMFloatType, LLVMDoubleType)) for ty in expected.arg_types)
            elif isinstance(expected, (LLVMFloatType, LLVMDoubleType)):
                is_float = True
        return get_builtin_op_type(op, is_float)

    def _cast_if_needed(self, val: LLVMTerm, target_ty: LLVMType) -> LLVMTerm:
        if val.type == target_ty:
            return val
        return LLVMCast(target_ty, val)

    def _get_target_name(self, target: LLVMTerm) -> str:
        if isinstance(target, LLVMVar):
            return target.name.name
        if isinstance(target, LLVMCall):
            return self._get_target_name(target.target)
        return ""

    def _is_inlinable_anf(self, name: Name, val: LLVMTerm) -> bool:
        if not name.name.startswith("anf"):
            return False
        is_partial = isinstance(val, LLVMCall) and isinstance(val.type, LLVMFunctionType)
        target = self._get_target_name(val) if isinstance(val, LLVMVar) else ""
        if isinstance(val, LLVMCall):
            target = self._get_target_name(val.target)
        is_op = (isinstance(val, LLVMVar) or (isinstance(val, LLVMCall) and is_partial)) and (
            target in BINARY_OPS or target in UNARY_OPS
        )
        is_vec = (isinstance(val, LLVMVar) or (isinstance(val, LLVMCall) and is_partial)) and target in (
            VECTOR_OPERATIONS | {"Vector_set", "Vector_get"}
        )
        is_math = (isinstance(val, LLVMVar) or (isinstance(val, LLVMCall) and is_partial)) and target.startswith(
            "Math_"
        )
        if is_math and is_partial:
            return False
        return is_partial or is_op or is_vec or is_math

    def _lower_as_standalone(
        self,
        term: Term | LLVMTerm,
        expected: LLVMType | None,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
        in_vec: bool = False,
    ) -> LLVMTerm:
        if isinstance(term, LLVMTerm):
            return term
        if isinstance(term, Abstraction):
            return self._lower_function(term, expected, type_env, env, allowed, in_vec)
        lowered = self._lower_term(term, expected, type_env, env, allowed, in_vector_op=in_vec)
        if isinstance(lowered, LLVMCall) and isinstance(lowered.type, LLVMFunctionType):
            return self._create_wrapper_function(lowered)
        return lowered

    def _lower_function(
        self,
        abs_term: Abstraction,
        expected: LLVMType | None,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
        in_vec: bool,
    ) -> LLVMFunction:
        arg_names: list[Name] = []
        curr: Term = abs_term
        while isinstance(curr, Abstraction):
            arg_names.append(curr.var_name)
            curr = curr.body

        param_tys, ret_ty = self.get_signature(
            expected.element_type
            if isinstance(expected, LLVMPointerType) and isinstance(expected.element_type, LLVMFunctionType)
            else expected or LLVMInt
        )
        param_tys = (param_tys + [LLVMInt] * len(arg_names))[: len(arg_names)]

        new_type_env = type_env.copy()
        resolved_tys = []
        for name, p_ty in zip(arg_names, param_tys):
            actual_ty = _generic_ptr if isinstance(p_ty, LLVMVoidType) else p_ty
            new_type_env[name] = actual_ty
            resolved_tys.append(actual_ty)

        body = self._lower_term(curr, ret_ty, new_type_env, env, allowed, in_vector_op=in_vec)
        return LLVMFunction(LLVMFunctionType(resolved_tys, ret_ty), arg_names, resolved_tys, body)

    def _create_wrapper_function(self, call: LLVMCall) -> LLVMFunction:
        params, ret = self.get_signature(call.type)
        names = [Name(f"wrapper_arg_{i}") for i in range(len(params))]
        args = call.args + [LLVMVar(ty, n) for n, ty in zip(names, params)]
        return LLVMFunction(call.type, names, params, LLVMCall(ret, call.target, args))

    def _uncurry(self, app: Application) -> tuple[Term, List[Term]]:
        args: list[Term] = []
        curr: Term = app
        while isinstance(curr, Application):
            args.append(curr.arg)
            curr = curr.fun
        args.reverse()
        return curr, args

    def _lower_args(
        self,
        args: list[Term],
        expected_params: list[LLVMType],
        offset: int,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
        in_vec: bool,
    ) -> list[LLVMTerm]:
        lowered_args = []
        for i, arg in enumerate(args):
            idx = offset + i
            exp = expected_params[idx] if idx < len(expected_params) else None
            if isinstance(arg, Annotation):
                exp = to_llvm_type(arg.type)
                arg = arg.expr
            lowered_args.append(self._lower_term(arg, exp, type_env, env, allowed, in_vector_op=in_vec))
        return lowered_args

    def _lower_vector_op(
        self,
        op: str,
        args: list[Term | LLVMTerm],
        expected: LLVMType | None,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
    ) -> LLVMTerm:
        def low_term(term, exp=None):
            return self._lower_term(term, exp, type_env, env, allowed, in_vector_op=True)

        if op == "Vector_reduce":
            kernel_term, init_term, vector_term, size_term = args
            low_vec, low_init, low_size = low_term(vector_term), low_term(init_term), low_term(size_term, LLVMInt)
            element_type = self._get_vector_base_type(low_vec.type)
            vec_cast = self._cast_if_needed(low_vec, LLVMPointerType(element_type))
            kernel = self._lower_as_standalone(
                kernel_term,
                LLVMFunctionType([low_init.type, element_type], low_init.type),
                type_env,
                env,
                allowed,
                True,
            )
            return LLVMVectorReduce(low_init.type, kernel, low_init, vec_cast, low_size)

        if op == "Vector_zipWith":
            kernel_term, v1_term, v2_term, size_term = args
            v1_low, v2_low, sz_low = low_term(v1_term), low_term(v2_term), low_term(size_term, LLVMInt)
            res_el = expected.element_type if expected and isinstance(expected, LLVMPointerType) else LLVMInt
            el1, el2 = self._get_vector_base_type(v1_low.type), self._get_vector_base_type(v2_low.type)
            v1_cast, v2_cast = (
                self._cast_if_needed(v1_low, LLVMPointerType(el1)),
                self._cast_if_needed(v2_low, LLVMPointerType(el2)),
            )
            kernel = self._lower_as_standalone(
                kernel_term, LLVMFunctionType([el1, el2], res_el), type_env, env, allowed, True
            )
            assert isinstance(kernel.type, LLVMFunctionType)
            return LLVMVectorZipWith(LLVMPointerType(kernel.type.return_type), kernel, v1_cast, v2_cast, sz_low)

        kernel_term, vector_term, size_term = args
        v_low, sz_low = low_term(vector_term), low_term(size_term, LLVMInt)
        element_type = self._get_vector_base_type(v_low.type)
        vec_cast = self._cast_if_needed(v_low, LLVMPointerType(element_type))

        if op in ("Vector_filter", "Vector_count"):
            res_el = LLVMBool
        elif expected and isinstance(expected, LLVMPointerType):
            res_el = expected.element_type
        else:
            k_lowered = self._lower_as_standalone(kernel_term, None, type_env, env, allowed, True)
            res_el = k_lowered.type.return_type if isinstance(k_lowered.type, LLVMFunctionType) else LLVMInt

        k_params = [LLVMInt, element_type] if op == "Vector_imap" else [element_type]
        kernel = self._lower_as_standalone(
            kernel_term, LLVMFunctionType(k_params, res_el), type_env, env, allowed, True
        )

        if op == "Vector_filter":
            return LLVMVectorFilter(vec_cast.type, kernel, vec_cast, sz_low)
        if op == "Vector_count":
            return LLVMVectorCount(LLVMInt, kernel, vec_cast, sz_low)

        assert isinstance(kernel.type, LLVMFunctionType)
        res_vec_ty = LLVMPointerType(kernel.type.return_type)
        return (
            LLVMVectorMap(res_vec_ty, kernel, vec_cast, sz_low)
            if op == "Vector_map"
            else LLVMVectorIMap(res_vec_ty, kernel, vec_cast, sz_low)
        )

    def _lower_term(
        self,
        term: Term | LLVMTerm,
        expected: LLVMType | None = None,
        type_env: Dict[Name, LLVMType] = None,
        env: Dict[Name, LLVMTerm] = None,
        allowed: set[Name] = None,
        in_vector_op: bool = False,
    ) -> LLVMTerm:
        if isinstance(term, LLVMTerm):
            return term
        type_env, env, allowed = type_env or {}, env or {}, allowed or set()

        match term:
            case Literal(val, ty):
                return LLVMLiteral(to_llvm_type(ty), val)
            case Var(name):
                return self._lower_var(name, expected, type_env, env)
            case Annotation(e, ty) | TypeApplication(e, ty):
                return self._lower_term(e, to_llvm_type(ty), type_env, env, allowed, in_vector_op)
            case TypeAbstraction(_, _, body):
                return self._lower_term(body, expected, type_env, env, allowed, in_vector_op)
            case Abstraction(_, _):
                return self._lower_as_standalone(term, expected, type_env, env, allowed, in_vector_op)
            case Application(_, _):
                return self._lower_app(term, expected, type_env, env, allowed, in_vector_op)
            case Let(name, val, body):
                return self._lower_let(name, val, body, expected, type_env, env, allowed, in_vector_op)
            case Rec(name, ty, val, body):
                return self._lower_rec(name, ty, val, body, expected, type_env, env, allowed, in_vector_op)
            case If(cond, then_t, else_t):
                return self._lower_if(cond, then_t, else_t, expected, type_env, env, allowed, in_vector_op)
            case _:
                raise LLVMLoweringError(f"could not lower term {term}")

    def _lower_var(
        self, name: Name, expected: LLVMType | None, type_env: Dict[Name, LLVMType], env: Dict[Name, LLVMTerm]
    ) -> LLVMTerm:
        if name.name in BINARY_OPS or name.name in UNARY_OPS:
            return LLVMVar(self._get_operator_type(name.name, expected), name)

        if name.name in BUILTIN_FUNCTION_TYPES:
            ty = BUILTIN_FUNCTION_TYPES[name.name]
            if expected and isinstance(expected, LLVMFunctionType) and len(expected.arg_types) == len(ty.arg_types):
                ty = expected
            elif expected and name.name == "Vector_new" and isinstance(expected, LLVMPointerType):
                ty = LLVMFunctionType([], expected)
            return LLVMVar(ty, name)

        if name in env:
            return env[name]
        for en, term in env.items():
            if en.name == name.name:
                return term

        var_ty = type_env.get(name) or expected or LLVMInt
        return LLVMVar(var_ty, name)

    def _lower_if(
        self,
        cond: Term,
        then_t: Term,
        else_t: Term,
        expected: LLVMType | None,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
        in_vec: bool,
    ) -> LLVMIf:
        low_cond = self._lower_term(cond, None, type_env, env, allowed, in_vec)
        low_then = self._lower_term(then_t, expected, type_env, env, allowed, in_vec)
        low_else = self._lower_term(else_t, expected, type_env, env, allowed, in_vec)
        return LLVMIf(low_then.type, low_cond, low_then, low_else)

    def _lower_app(
        self,
        t: Application,
        expected: LLVMType | None,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
        in_vec: bool,
    ) -> LLVMTerm:
        base, args = self._uncurry(t)
        lowered_base = self._lower_term(base, None, type_env, env, allowed, in_vector_op=in_vec)
        if not lowered_base:
            raise LLVMBackendError(f"could not lower base {base}")

        target, prev_args, eff_ty = self._extract_call_info(lowered_base)
        params, ret = self.get_signature(eff_ty)
        lookup = self._get_lookup_name(target)

        if lookup in BUILTIN_FUNCTION_TYPES or lookup in VECTOR_OPERATIONS:
            return self._lower_builtin_call(lookup, target, prev_args, args, expected, type_env, env, allowed, in_vec)

        all_args = prev_args + self._lower_args(args, params, len(prev_args), type_env, env, allowed, in_vec)
        return self._create_call_or_partial(target, all_args, params, ret)

    def _lower_builtin_call(
        self,
        name: str,
        target: LLVMTerm,
        prev_args: list[LLVMTerm],
        args: list[Term],
        expected: LLVMType | None,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
        in_vec: bool,
    ) -> LLVMTerm:
        params, ret = self.get_signature(target.type)

        is_full_v = self._is_full_vector_op(name, len(prev_args) + len(args))
        if (in_vec or name in VECTOR_OPERATIONS) and is_full_v:
            return self._lower_vector_op(name, list(prev_args) + list(args), expected, type_env, env, allowed)

        all_args = prev_args + self._lower_args(args, params, len(prev_args), type_env, env, allowed, in_vec)

        if name in POLYMORPHIC_FUNCTIONS:
            if name.startswith("Math"):
                all_args = [self._cast_if_needed(a, p) for a, p in zip(all_args, params)]
                return LLVMCall(ret, target, all_args)

            if name == "Vector_get" and len(all_args) == 2:
                return self._lower_vector_get(all_args[0], all_args[1])

            if name == "Vector_set" and len(all_args) == 3:
                return self._lower_vector_set(all_args[0], all_args[1], all_args[2])

        return self._create_call_or_partial(target, all_args, params, ret)

    def _extract_call_info(self, lowered: LLVMTerm) -> tuple[LLVMTerm, list[LLVMTerm], LLVMType]:
        if isinstance(lowered, LLVMCall) and isinstance(lowered.type, LLVMFunctionType):
            return lowered.target, lowered.args, lowered.type
        return lowered, [], lowered.type

    def _get_lookup_name(self, target: LLVMTerm) -> str:
        name = self._get_target_name(target)
        return name.rsplit("_", 1)[0] if name.rsplit("_", 1)[-1].isdigit() else name

    def _is_full_vector_op(self, op: str, total_args: int) -> bool:
        if op not in VECTOR_OPERATIONS:
            return False
        threshold = 4 if op in ("Vector_reduce", "Vector_zipWith") else 3
        return total_args >= threshold

    def _lower_vector_get(self, vec: LLVMTerm, idx: LLVMTerm) -> LLVMLoad:
        el = self._get_vector_base_type(vec.type)
        ptr_ty = LLVMPointerType(el)
        vec_ptr = self._cast_if_needed(vec, ptr_ty)
        return LLVMLoad(el, LLVMGetElementPtr(ptr_ty, vec_ptr, [idx]))

    def _lower_vector_set(self, vec: LLVMTerm, idx: LLVMTerm, val: LLVMTerm) -> LLVMStore:
        el = self._get_vector_base_type(vec.type)
        ptr_ty = LLVMPointerType(el)
        vec_ptr = self._cast_if_needed(vec, ptr_ty)
        val_cast = self._cast_if_needed(val, el)
        return LLVMStore(vec.type, val_cast, LLVMGetElementPtr(ptr_ty, vec_ptr, [idx]))

    def _create_call_or_partial(
        self, target: LLVMTerm, args: list[LLVMTerm], params: list[LLVMType], ret: LLVMType
    ) -> LLVMCall:
        if len(args) < len(params):
            return LLVMCall(LLVMFunctionType(params[len(args) :], ret), target, args)
        return LLVMCall(ret, target, args)

    def _lower_let(
        self,
        name: Name,
        val: Term,
        body: Term,
        expected: LLVMType | None,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
        in_vec: bool,
    ) -> LLVMTerm:
        lowered_val = self._lower_term(val, None, type_env, env, allowed, in_vector_op=in_vec)
        if isinstance(lowered_val, LLVMFunction):
            lowered_val.name = name
        new_ty_env = {**type_env, name: lowered_val.type if lowered_val else LLVMInt}
        new_env = env.copy()
        if lowered_val and self._is_inlinable_anf(name, lowered_val):
            new_env[name] = lowered_val
        else:
            new_env[name] = LLVMVar(new_ty_env[name], name)
        lowered_body = self._lower_term(body, expected, new_ty_env, new_env, allowed, in_vector_op=in_vec)
        return (
            lowered_body
            if self._is_inlinable_anf(name, lowered_val)
            else LLVMLet(lowered_body.type, name, lowered_val, lowered_body)
        )

    def _lower_rec(
        self,
        name: Name,
        ty: Type,
        val: Term,
        body: Term,
        expected: LLVMType | None,
        type_env: Dict[Name, LLVMType],
        env: Dict[Name, LLVMTerm],
        allowed: set[Name],
        in_vec: bool,
    ) -> LLVMLet:
        func_type = to_llvm_type(ty)
        params, ret_ty = self.get_signature(func_type)
        flat_func_type = LLVMFunctionType(params, ret_ty)
        new_ty_env, new_env = {**type_env, name: flat_func_type}, {**env, name: LLVMVar(flat_func_type, name)}
        lowered_val = self._lower_term(val, flat_func_type, new_ty_env, new_env, allowed, in_vector_op=in_vec)
        if isinstance(lowered_val, LLVMFunction):
            lowered_val.name = name
        lowered_body = self._lower_term(body, expected, new_ty_env, new_env, allowed, in_vector_op=in_vec)
        return LLVMLet(lowered_body.type, name, lowered_val, lowered_body)
