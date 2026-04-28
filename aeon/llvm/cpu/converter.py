from __future__ import annotations

import llvmlite.binding as llvm
import llvmlite.ir as ir

from aeon.llvm.core import LLVMIRGenerator, LLVMBackendError, LLVMVisitor
from aeon.llvm.llvm_ast import (
    LLVMTerm,
    LLVMType,
    LLVMIntType,
    LLVMFloatType,
    LLVMDoubleType,
    LLVMBoolType,
    LLVMCharType,
    LLVMVoidType,
    LLVMPointerType,
    LLVMFunctionType,
    LLVMLiteral,
    LLVMVar,
    LLVMIf,
    LLVMLet,
    LLVMFunction,
    LLVMCall,
    LLVMGetElementPtr,
    LLVMLoad,
    LLVMStore,
    LLVMAlloc,
    LLVMVectorMap,
    LLVMVectorReduce,
    LLVMVectorIMap,
    LLVMVectorFilter,
    LLVMVectorZipWith,
    LLVMVectorCount,
    LLVMVectorGet,
    LLVMVectorSet,
    VECTOR_OPERATIONS,
    LLVMCast,
)
from aeon.llvm.utils import BINARY_OPS, UNARY_OPS, sanitize_name
from aeon.utils.name import Name

from contextlib import contextmanager
from abc import ABC, abstractmethod
from typing import Dict, Any, Callable


class LLVMIRGenerationError(LLVMBackendError):
    pass


class TypeCaster:
    def __init__(self):
        self.casters = []
        self.register_defaults()

    def register(self, predicate, cast_func):
        self.casters.insert(0, (predicate, cast_func))

    def register_defaults(self):
        self.register(lambda v_ty, t_ty: isinstance(v_ty, ir.VoidType), lambda b, v, t_ty: ir.Constant(t_ty, None))
        self.register(
            lambda v_ty, t_ty: isinstance(v_ty, ir.IntType) and isinstance(t_ty, (ir.FloatType, ir.DoubleType)),
            lambda b, v, t_ty: b.sitofp(v, t_ty),
        )
        self.register(
            lambda v_ty, t_ty: isinstance(v_ty, (ir.FloatType, ir.DoubleType)) and isinstance(t_ty, ir.IntType),
            lambda b, v, t_ty: b.fptosi(v, t_ty),
        )
        self.register(
            lambda v_ty, t_ty: isinstance(v_ty, ir.FloatType) and isinstance(t_ty, ir.DoubleType),
            lambda b, v, t_ty: b.fpext(v, t_ty),
        )
        self.register(
            lambda v_ty, t_ty: isinstance(v_ty, ir.DoubleType) and isinstance(t_ty, ir.FloatType),
            lambda b, v, t_ty: b.fptrunc(v, t_ty),
        )
        self.register(
            lambda v_ty, t_ty: (
                isinstance(v_ty, ir.IntType) and isinstance(t_ty, ir.IntType) and v_ty.width > t_ty.width
            ),
            lambda b, v, t_ty: b.trunc(v, t_ty),
        )
        self.register(
            lambda v_ty, t_ty: (
                isinstance(v_ty, ir.IntType) and isinstance(t_ty, ir.IntType) and v_ty.width < t_ty.width
            ),
            lambda b, v, t_ty: b.zext(v, t_ty),
        )
        self.register(
            lambda v_ty, t_ty: isinstance(v_ty, ir.PointerType) and isinstance(t_ty, ir.PointerType),
            lambda b, v, t_ty: b.bitcast(v, t_ty),
        )
        self.register(
            lambda v_ty, t_ty: isinstance(v_ty, ir.PointerType) and isinstance(t_ty, ir.IntType),
            lambda b, v, t_ty: b.ptrtoint(v, t_ty),
        )
        self.register(
            lambda v_ty, t_ty: isinstance(v_ty, ir.IntType) and isinstance(t_ty, ir.PointerType),
            lambda b, v, t_ty: b.inttoptr(v, t_ty),
        )

    def cast(self, builder: ir.IRBuilder, val: ir.Value, target_ty: ir.Type) -> ir.Value:
        if val.type == target_ty:
            return val
        for predicate, cast_func in self.casters:
            if predicate(val.type, target_ty):
                return cast_func(builder, val, target_ty)
        return builder.bitcast(val, target_ty)


class OperatorStrategy:
    def __init__(self):
        self.ops = {}
        self.register_defaults()

    def register(self, op_name, func):
        self.ops[op_name] = func

    def register_defaults(self):
        self.register("+", lambda b, v, is_f: b.fadd(v[0], v[1]) if is_f else b.add(v[0], v[1]))
        self.register(
            "-",
            lambda b, v, is_f: (
                (b.fsub(v[0], v[1]) if len(v) == 2 else b.fneg(v[0]))
                if is_f
                else (b.sub(v[0], v[1]) if len(v) == 2 else b.sub(ir.Constant(v[0].type, 0), v[0]))
            ),
        )
        self.register("*", lambda b, v, is_f: b.fmul(v[0], v[1]) if is_f else b.mul(v[0], v[1]))
        self.register("/", lambda b, v, is_f: b.fdiv(v[0], v[1]) if is_f else b.sdiv(v[0], v[1]))
        self.register("%", lambda b, v, is_f: b.frem(v[0], v[1]) if is_f else b.srem(v[0], v[1]))
        self.register(
            "==", lambda b, v, is_f: b.fcmp_ordered("==", v[0], v[1]) if is_f else b.icmp_signed("==", v[0], v[1])
        )
        self.register(
            "!=", lambda b, v, is_f: b.fcmp_ordered("!=", v[0], v[1]) if is_f else b.icmp_signed("!=", v[0], v[1])
        )
        self.register(
            "<", lambda b, v, is_f: b.fcmp_ordered("<", v[0], v[1]) if is_f else b.icmp_signed("<", v[0], v[1])
        )
        self.register(
            "<=", lambda b, v, is_f: b.fcmp_ordered("<=", v[0], v[1]) if is_f else b.icmp_signed("<=", v[0], v[1])
        )
        self.register(
            ">", lambda b, v, is_f: b.fcmp_ordered(">", v[0], v[1]) if is_f else b.icmp_signed(">", v[0], v[1])
        )
        self.register(
            ">=", lambda b, v, is_f: b.fcmp_ordered(">=", v[0], v[1]) if is_f else b.icmp_signed(">=", v[0], v[1])
        )
        self.register("&&", lambda b, v, is_f: b.and_(v[0], v[1]))
        self.register("||", lambda b, v, is_f: b.or_(v[0], v[1]))
        self.register("!", lambda b, v, is_f: b.not_(v[0]))

    def execute(self, builder: ir.IRBuilder, op: str, vals: list[ir.Value], is_f: bool) -> ir.Value | None:
        if op in self.ops:
            return self.ops[op](builder, vals, is_f)
        return None


class VectorExecutor(ABC):
    def __init__(self, generator):
        self.gen = generator

    @abstractmethod
    def execute(self, size_val: ir.Value, name: str, body_fn: Callable[[ir.Value], None]):
        pass


class CPULoopExecutor(VectorExecutor):
    def execute(self, size_val: ir.Value, name: str, body_fn: Callable[[ir.Value], None]):
        self.gen.to_ir_loop(size_val, name, body_fn)


class CPULLVMIRGenerator(LLVMIRGenerator, LLVMVisitor):
    def __init__(self):
        llvm.initialize_native_target()
        llvm.initialize_native_asmprinter()

        self.module = ir.Module(name="aeon_cpu_module")
        self.module.triple = llvm.get_process_triple()
        target = llvm.Target.from_triple(self.module.triple)
        target_machine = target.create_target_machine()
        self.module.data_layout = str(target_machine.target_data)
        self.target_data = target_machine.target_data

        self.builder = None
        self.env = {}
        self.fn_count = 0
        self._is_top_level = False

        self.type_caster = TypeCaster()
        self.op_strategy = OperatorStrategy()
        self.vector_executor = CPULoopExecutor(self)

    @contextmanager
    def _push_scope(self):
        old_builder = self.builder
        old_env = self.env.copy()
        old_is_top_level = self._is_top_level
        try:
            yield
        finally:
            self.builder = old_builder
            self.env = old_env
            self._is_top_level = old_is_top_level

    def to_ir_type(self, ty: LLVMType) -> ir.Type:
        return ty.to_ir()

    def _heap_alloc(self, element_ty: ir.Type, count: ir.Value) -> ir.Value:
        element_size = element_ty.get_abi_size(self.target_data)

        count_i64 = self.builder.sext(count, ir.IntType(64)) if count.type.width < 64 else count
        total_size = self.builder.mul(count_i64, ir.Constant(ir.IntType(64), element_size))

        malloc_ty = ir.FunctionType(ir.PointerType(ir.IntType(8)), [ir.IntType(64)])
        malloc_func = self.module.globals.get("malloc")
        if not malloc_func:
            malloc_func = ir.Function(self.module, malloc_ty, name="malloc")

        raw_ptr = self.builder.call(malloc_func, [total_size])
        return self.builder.bitcast(raw_ptr, ir.PointerType(element_ty))

    def generate_ir(self, definitions: list[LLVMTerm], initial_env: Dict[str, Any] = None) -> str:
        if initial_env:
            self.env.update(initial_env)

        for kernel_ast in definitions:
            if isinstance(kernel_ast, LLVMFunction) and kernel_ast.name:
                func_name = sanitize_name(kernel_ast.name)
                if func_name not in self.module.globals:
                    func_type = self.to_ir_type(kernel_ast.type)
                    func = ir.Function(self.module, func_type, name=func_name)
                    self.env[func_name] = func

        for kernel_ast in definitions:
            self._is_top_level = True
            kernel_ast.accept(self)
        return str(self.module)

    def declare_external(self, name: Name, ty: LLVMType):
        str_name = sanitize_name(name)
        if str_name in self.module.globals:
            return
        ir_type = self.to_ir_type(ty)
        ir.Function(self.module, ir_type, name=str_name)

    def visit(self, node: LLVMTerm) -> ir.Value | None:
        if node is None:
            return None
        return node.accept(self)

    def visit_literal(self, node: LLVMLiteral) -> ir.Value:
        result_type, value = node.type, node.value
        ir_type = self.to_ir_type(result_type)
        match result_type:
            case LLVMBoolType():
                return ir.Constant(ir.IntType(1), 1 if value else 0)
            case LLVMIntType(bits):
                return ir.Constant(ir.IntType(bits), int(value))
            case LLVMFloatType() | LLVMDoubleType():
                return ir.Constant(ir_type, float(value))
            case LLVMCharType():
                return ir.Constant(ir.IntType(8), ord(value))
            case LLVMPointerType(element_type=LLVMCharType()):
                if isinstance(value, str):
                    text = value + "\0"
                    c_str = ir.Constant(ir.ArrayType(ir.IntType(8), len(text)), bytearray(text, "utf-8"))
                    gv = ir.GlobalVariable(self.module, c_str.type, name=f"str_const_{self.fn_count}")
                    self.fn_count += 1
                    gv.global_constant = True
                    gv.initializer = c_str
                    zero = ir.Constant(ir.IntType(32), 0)
                    return self.builder.gep(gv, [zero, zero]) if self.builder else gv
                raise LLVMIRGenerationError(f"unsupported pointer literal {value}")
            case _:
                raise LLVMIRGenerationError(f"unsupported literal type {result_type}")

    def visit_var(self, node: LLVMVar) -> ir.Value:
        var_name, result_type = node.name, node.type
        str_name = sanitize_name(var_name)
        if str_name in self.env:
            return self.env[str_name]
        if str_name in self.module.globals:
            return self.module.globals[str_name]

        base_name = var_name.name
        if base_name == "Math_PI":
            return ir.Constant(ir.DoubleType(), 3.141592653589793)

        builtin_map = {
            "Math_pow": "pow",
            "Math_powf": "pow",
            "Math_sqrt": "sqrt",
            "Math_sqrtf": "sqrt",
            "Math_sin": "sin",
            "Math_cos": "cos",
            "Math_exp": "exp",
            "Math_log": "log",
        }

        name_parts = str_name.rsplit("_", 1)
        lookup_name = name_parts[0] if len(name_parts) > 1 and name_parts[1].isdigit() else str_name

        actual_name = builtin_map.get(lookup_name, lookup_name)

        if (
            actual_name in {"pow", "sqrt", "sin", "cos", "exp", "log", "malloc", "free", "printf", "native"}
            or lookup_name in VECTOR_OPERATIONS
        ):
            if actual_name in self.module.globals:
                return self.module.globals[actual_name]

            actual_ty = result_type
            if actual_name == "native" and not isinstance(actual_ty, LLVMFunctionType):
                actual_ty = LLVMFunctionType(
                    [LLVMPointerType(element_type=LLVMCharType())], LLVMPointerType(element_type=LLVMCharType())
                )

            return ir.Function(self.module, self.to_ir_type(actual_ty), name=actual_name)

        raise LLVMIRGenerationError(f"undefined variable {str_name}")

    def visit_if(self, node: LLVMIf) -> ir.Value | None:
        if self.builder is None:
            return None
        result_type, cond, then_t, else_t = node.type, node.cond, node.then_t, node.else_t
        cond_val = cond.accept(self)

        with self.builder.if_else(cond_val) as (then_block, else_block):
            with then_block:
                self._is_top_level = False
                then_val = then_t.accept(self)
                then_exit = self.builder.basic_block
            with else_block:
                self._is_top_level = False
                else_val = else_t.accept(self)
                else_exit = self.builder.basic_block

        if isinstance(result_type, LLVMVoidType):
            return None

        phi = self.builder.phi(self.to_ir_type(result_type), name="if_res")
        phi.add_incoming(then_val if then_val is not None else ir.Constant(phi.type, 0), then_exit)
        phi.add_incoming(else_val if else_val is not None else ir.Constant(phi.type, 0), else_exit)
        return phi

    def visit_let(self, node: LLVMLet) -> ir.Value | None:
        var_name, var_value, body = node.var_name, node.var_value, node.body
        str_name = sanitize_name(var_name)

        if isinstance(var_value, LLVMFunction):
            var_value.name = var_name
            with self._push_scope():
                self._is_top_level = False
                func = var_value.accept(self)

            with self._push_scope():
                self.env[str_name] = func
                return body.accept(self)

        with self._push_scope():
            self._is_top_level = False
            val_gen = var_value.accept(self)

        with self._push_scope():
            self.env[str_name] = val_gen
            return body.accept(self)

    def visit_function(self, node: LLVMFunction) -> ir.Function:
        function_type, arg_names, body, function_name = node.type, node.arg_names, node.body, node.name
        func_name = sanitize_name(function_name) if function_name else f"anon_func_{self.fn_count}"
        if not function_name:
            self.fn_count += 1

        func = self.module.globals.get(func_name) or ir.Function(
            self.module, self.to_ir_type(function_type), name=func_name
        )

        with self._push_scope():
            self.env[func_name] = func
            self.builder = ir.IRBuilder(func.append_basic_block(name="entry"))

            for i, arg_name in enumerate(arg_names):
                str_arg_name = sanitize_name(arg_name)
                func.args[i].name = str_arg_name
                self.env[str_arg_name] = func.args[i]

            self._is_top_level = False
            ret_val = body.accept(self)

            if isinstance(function_type, LLVMFunctionType) and isinstance(function_type.return_type, LLVMVoidType):
                self.builder.ret_void()
            else:
                if ret_val is not None:
                    ret_val = self._cast_if_needed(ret_val, func.function_type.return_type)
                self.builder.ret(ret_val)

        return func

    def visit_call(self, node: LLVMCall) -> ir.Value | None:
        if self.builder is None:
            return None
        target, args = node.target, node.args

        if isinstance(target, LLVMVar) and (target.name.name in BINARY_OPS or target.name.name in UNARY_OPS):
            return self.to_ir_operator(target.name.name, args)

        self._is_top_level = False
        target_func = target.accept(self)
        arg_vals = [arg.accept(self) for arg in args]
        if not target_func:
            return None

        if isinstance(target_func, ir.Function):
            if len(arg_vals) < len(target_func.function_type.args):
                return None
            new_arg_vals = []
            for arg_val, expected_ty in zip(arg_vals, target_func.function_type.args):
                new_arg_vals.append(self._cast_if_needed(arg_val, expected_ty))
            arg_vals = new_arg_vals

        return self.builder.call(target_func, arg_vals)

    def to_ir_operator(self, op: str, args: list[LLVMTerm]) -> ir.Value | None:
        self._is_top_level = False
        vals = [arg.accept(self) for arg in args]
        if any(v is None for v in vals):
            return None

        if len(vals) == 2:
            if vals[0].type != vals[1].type:
                if isinstance(vals[0].type, (ir.FloatType, ir.DoubleType)) or isinstance(
                    vals[1].type, (ir.FloatType, ir.DoubleType)
                ):
                    target_ty = (
                        vals[0].type if isinstance(vals[0].type, (ir.FloatType, ir.DoubleType)) else vals[1].type
                    )
                    if isinstance(vals[0].type, ir.DoubleType) or isinstance(vals[1].type, ir.DoubleType):
                        target_ty = ir.DoubleType()
                    vals[0] = self._cast_if_needed(vals[0], target_ty)
                    vals[1] = self._cast_if_needed(vals[1], target_ty)
                else:
                    w0 = vals[0].type.width if isinstance(vals[0].type, ir.IntType) else 0
                    w1 = vals[1].type.width if isinstance(vals[1].type, ir.IntType) else 0
                    target_ty = ir.IntType(max(w0, w1))
                    vals[0] = self._cast_if_needed(vals[0], target_ty)
                    vals[1] = self._cast_if_needed(vals[1], target_ty)

        is_f = isinstance(vals[0].type, (ir.FloatType, ir.DoubleType))
        return self.op_strategy.execute(self.builder, op, vals, is_f)

    def _cast_if_needed(self, val: ir.Value, target_ty: ir.Type) -> ir.Value:
        return self.type_caster.cast(self.builder, val, target_ty)

    def visit_cast(self, node: LLVMCast) -> ir.Value:
        val, ty = node.val, node.type
        self._is_top_level = False
        v_val = val.accept(self)
        target_ty = self.to_ir_type(ty)
        return self._cast_if_needed(v_val, target_ty)

    def visit_gep(self, node: LLVMGetElementPtr) -> ir.Value:
        ptr, indices = node.ptr, node.indices
        self._is_top_level = False
        return self.builder.gep(ptr.accept(self), [idx.accept(self) for idx in indices])

    def visit_load(self, node: LLVMLoad) -> ir.Value:
        self._is_top_level = False
        return self.builder.load(node.ptr.accept(self))

    def visit_store(self, node: LLVMStore) -> ir.Value:
        value, ptr = node.value, node.ptr
        self._is_top_level = False
        v_val = value.accept(self)
        p_val = ptr.accept(self)
        if not isinstance(v_val.type, ir.VoidType):
            self.builder.store(v_val, p_val)
        return p_val

    def visit_alloc(self, node: LLVMAlloc) -> ir.Value:
        ty = node.type
        alloc_ty = self.to_ir_type(ty.element_type if isinstance(ty, LLVMPointerType) else ty)
        return self.builder.alloca(alloc_ty)

    def to_ir_loop(self, size: ir.Value, name: str, body_fn: Callable[[ir.Value], None]):
        idx_ptr = self.builder.alloca(ir.IntType(32), name=f"{name}_idx")
        self.builder.store(ir.Constant(ir.IntType(32), 0), idx_ptr)

        cond_bb = self.builder.append_basic_block(f"{name}_cond")
        body_bb = self.builder.append_basic_block(f"{name}_body")
        end_bb = self.builder.append_basic_block(f"{name}_end")

        self.builder.branch(cond_bb)
        self.builder.position_at_end(cond_bb)

        curr_idx = self.builder.load(idx_ptr)
        is_less = self.builder.icmp_signed("<", curr_idx, size)
        self.builder.cbranch(is_less, body_bb, end_bb)

        self.builder.position_at_end(body_bb)
        body_fn(curr_idx)

        self.builder.store(self.builder.add(curr_idx, ir.Constant(ir.IntType(32), 1)), idx_ptr)
        self.builder.branch(cond_bb)
        self.builder.position_at_end(end_bb)

    def visit_vector_map(self, node: LLVMVectorMap) -> ir.Value:
        res_ty, f, v, size = node.type, node.f, node.v, node.size
        self._is_top_level = False
        f_val, v_val, size_val = f.accept(self), v.accept(self), size.accept(self)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._heap_alloc(res_base_ty, size_val)

        def body(idx):
            mapped_val = self.builder.call(f_val, [self.builder.load(self.builder.gep(v_val, [idx]))])
            if not isinstance(mapped_val.type, ir.VoidType):
                self.builder.store(mapped_val, self.builder.gep(new_v, [idx]))

        self.vector_executor.execute(size_val, "map", body)
        return new_v

    def visit_vector_reduce(self, node: LLVMVectorReduce) -> ir.Value:
        ty, f, initial, v, size = node.type, node.f, node.initial, node.v, node.size
        self._is_top_level = False
        f_val, init_val, v_val, size_val = f.accept(self), initial.accept(self), v.accept(self), size.accept(self)
        acc_ty = self.to_ir_type(ty)
        if isinstance(acc_ty, ir.VoidType):
            acc_ty = ir.IntType(32)

        acc_ptr = self.builder.alloca(acc_ty, name="reduce_acc")
        if init_val and not isinstance(init_val.type, ir.VoidType):
            self.builder.store(init_val, acc_ptr)

        def body(idx):
            new_acc = self.builder.call(
                f_val, [self.builder.load(acc_ptr), self.builder.load(self.builder.gep(v_val, [idx]))]
            )
            if not isinstance(new_acc.type, ir.VoidType):
                self.builder.store(new_acc, acc_ptr)

        self.vector_executor.execute(size_val, "reduce", body)
        return self.builder.load(acc_ptr)

    def visit_vector_imap(self, node: LLVMVectorIMap) -> ir.Value:
        res_ty, f, v, size = node.type, node.f, node.v, node.size
        self._is_top_level = False
        f_val, v_val, size_val = f.accept(self), v.accept(self), size.accept(self)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._heap_alloc(res_base_ty, size_val)

        def body(idx):
            mapped_val = self.builder.call(f_val, [idx, self.builder.load(self.builder.gep(v_val, [idx]))])
            if not isinstance(mapped_val.type, ir.VoidType):
                self.builder.store(mapped_val, self.builder.gep(new_v, [idx]))

        self.vector_executor.execute(size_val, "imap", body)
        return new_v

    def visit_vector_filter(self, node: LLVMVectorFilter) -> ir.Value:
        res_ty, f, v, size = node.type, node.f, node.v, node.size
        self._is_top_level = False
        f_val, v_val, size_val = f.accept(self), v.accept(self), size.accept(self)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._heap_alloc(res_base_ty, size_val)
        new_idx_ptr = self.builder.alloca(ir.IntType(32), name="filter_new_idx")
        self.builder.store(ir.Constant(ir.IntType(32), 0), new_idx_ptr)

        def body(idx):
            val = self.builder.load(self.builder.gep(v_val, [idx]))
            keep = self.builder.call(f_val, [val])
            with self.builder.if_then(self._cast_if_needed(keep, ir.IntType(1))):
                new_idx = self.builder.load(new_idx_ptr)
                self.builder.store(val, self.builder.gep(new_v, [new_idx]))
                self.builder.store(self.builder.add(new_idx, ir.Constant(ir.IntType(32), 1)), new_idx_ptr)

        self.vector_executor.execute(size_val, "filter", body)
        return new_v

    def visit_vector_zipwith(self, node: LLVMVectorZipWith) -> ir.Value:
        res_ty, f, v1, v2, size = node.type, node.f, node.v1, node.v2, node.size
        self._is_top_level = False
        f_val, v1_val, v2_val, size_val = f.accept(self), v1.accept(self), v2.accept(self), size.accept(self)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._heap_alloc(res_base_ty, size_val)

        def body(idx):
            val1 = self.builder.load(self.builder.gep(v1_val, [idx]))
            val2 = self.builder.load(self.builder.gep(v2_val, [idx]))
            res = self.builder.call(f_val, [val1, val2])
            self.builder.store(res, self.builder.gep(new_v, [idx]))

        self.vector_executor.execute(size_val, "zip", body)
        return new_v

    def visit_vector_count(self, node: LLVMVectorCount) -> ir.Value:
        f, v, size = node.f, node.v, node.size
        self._is_top_level = False
        f_val, v_val, size_val = f.accept(self), v.accept(self), size.accept(self)
        count_ptr = self.builder.alloca(ir.IntType(32), name="count_res")
        self.builder.store(ir.Constant(ir.IntType(32), 0), count_ptr)

        def body(idx):
            val = self.builder.load(self.builder.gep(v_val, [idx]))
            is_match = self.builder.call(f_val, [val])
            with self.builder.if_then(self._cast_if_needed(is_match, ir.IntType(1))):
                self.builder.store(
                    self.builder.add(self.builder.load(count_ptr), ir.Constant(ir.IntType(32), 1)), count_ptr
                )

        self.vector_executor.execute(size_val, "count", body)
        return self.builder.load(count_ptr)

    def visit_vector_get(self, node: LLVMVectorGet) -> ir.Value:
        self._is_top_level = False
        v_val = node.v.accept(self)
        idx_val = node.index.accept(self)
        ptr = self.builder.gep(v_val, [idx_val])
        return self.builder.load(ptr)

    def visit_vector_set(self, node: LLVMVectorSet) -> ir.Value:
        self._is_top_level = False
        v_val = node.v.accept(self)
        idx_val = node.index.accept(self)
        val_val = node.value.accept(self)
        ptr = self.builder.gep(v_val, [idx_val])
        self.builder.store(self._cast_if_needed(val_val, ptr.type.pointee), ptr)
        return v_val
