from __future__ import annotations

import llvmlite.binding as llvm
import llvmlite.ir as ir

from aeon.llvm.core import LLVMIRGenerator, LLVMBackendError
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
    LLVMArrayType,
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
    VECTOR_OPERATIONS,
    LLVMCast,
)
from aeon.llvm.utils import BINARY_OPS, UNARY_OPS, sanitize_name
from aeon.utils.name import Name
from typing import Dict, Any, Callable


class LLVMIRGenerationError(LLVMBackendError):
    pass


class CPULLVMIRGenerator(LLVMIRGenerator):
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

    def to_ir_type(self, ty: LLVMType) -> ir.Type:
        match ty:
            case LLVMIntType(bits):
                return ir.IntType(bits)
            case LLVMFloatType():
                return ir.FloatType()
            case LLVMDoubleType():
                return ir.DoubleType()
            case LLVMBoolType():
                return ir.IntType(1)
            case LLVMCharType():
                return ir.IntType(8)
            case LLVMVoidType():
                return ir.IntType(32)
            case LLVMFunctionType(arg_types, return_type):
                ir_return_type = (
                    ir.VoidType() if isinstance(return_type, LLVMVoidType) else self.to_ir_type(return_type)
                )
                ir_arg_types = [self.to_ir_type(arg) for arg in arg_types]
                return ir.FunctionType(ir_return_type, ir_arg_types)
            case LLVMPointerType(element_type, address_space):
                ir_base = self.to_ir_type(element_type)
                if isinstance(ir_base, ir.VoidType):
                    ir_base = ir.IntType(8)
                return ir.PointerType(ir_base, address_space.value)
            case LLVMArrayType(element_type, size):
                ir_base = self.to_ir_type(element_type)
                return ir.ArrayType(ir_base, size if size is not None else 0)
            case _:
                raise LLVMIRGenerationError(f"unsupported LLVM type {ty}")

    def _heap_alloc(self, element_ty: ir.Type, count: ir.Value) -> ir.Value:
        element_size = self.target_data.get_abi_size(element_ty)

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
            self.to_ir(kernel_ast, is_top_level=True)
        return str(self.module)

    def declare_external(self, name: Name, ty: LLVMType):
        str_name = sanitize_name(name)
        if str_name in self.module.globals:
            return
        ir_type = self.to_ir_type(ty)
        ir.Function(self.module, ir_type, name=str_name)

    def to_ir(self, llvm_ast: LLVMTerm, is_top_level: bool) -> ir.Value | None:
        if llvm_ast is None:
            return None

        match llvm_ast:
            case LLVMLiteral(type=ty, value=val):
                return self.to_ir_literal(ty, val)

            case LLVMVar(type=ty, name=name):
                return self.to_ir_variable(ty, name)

            case LLVMIf(type=ty, cond=cond, then_t=then_t, else_t=else_t):
                return self.to_ir_if(ty, cond, then_t, else_t)

            case LLVMLet(type=ty, var_name=name, var_value=val, body=body):
                return self.to_ir_let(name, val, body, is_top_level)

            case LLVMFunction(type=ty, arg_names=names, body=body, name=opt_name):
                return self.to_ir_function(ty, names, body, opt_name)

            case LLVMCall(type=_, target=target, args=args):
                return self.to_ir_call(target, args)

            case LLVMCast(type=ty, val=val):
                v_val = self.to_ir(val, False)
                target_ty = self.to_ir_type(ty)
                if v_val.type == target_ty:
                    return v_val
                if isinstance(v_val.type, ir.IntType) and isinstance(target_ty, (ir.FloatType, ir.DoubleType)):
                    return self.builder.sitofp(v_val, target_ty)
                if isinstance(v_val.type, (ir.FloatType, ir.DoubleType)) and isinstance(target_ty, ir.IntType):
                    return self.builder.fptosi(v_val, target_ty)
                if isinstance(v_val.type, ir.FloatType) and isinstance(target_ty, ir.DoubleType):
                    return self.builder.fpext(v_val, target_ty)
                if isinstance(v_val.type, ir.DoubleType) and isinstance(target_ty, ir.FloatType):
                    return self.builder.fptrunc(v_val, target_ty)
                return self.builder.bitcast(v_val, target_ty)

            case LLVMGetElementPtr(ptr=ptr, indices=indices):
                return self.builder.gep(self.to_ir(ptr, False), [self.to_ir(i, False) for i in indices])

            case LLVMLoad(ptr=ptr):
                return self.builder.load(self.to_ir(ptr, False))

            case LLVMStore(value=value, ptr=ptr):
                v_val = self.to_ir(value, False)
                p_val = self.to_ir(ptr, False)
                return p_val if isinstance(v_val.type, ir.VoidType) else self.builder.store(v_val, p_val)

            case LLVMAlloc(type=ty):
                alloc_ty = self.to_ir_type(ty.element_type if isinstance(ty, LLVMPointerType) else ty)
                return self.builder.alloca(alloc_ty)

            case LLVMVectorMap(type=res_ty, f=f, v=v, size=size):
                return self.to_ir_vector_map(res_ty, f, v, size)

            case LLVMVectorReduce(type=ty, f=f, initial=initial, v=v, size=size):
                return self.to_ir_vector_reduce(ty, f, initial, v, size)

            case LLVMVectorIMap(type=res_ty, f=f, v=v, size=size):
                return self.to_ir_vector_imap(res_ty, f, v, size)

            case LLVMVectorFilter(type=res_ty, f=f, v=v, size=size):
                return self.to_ir_vector_filter(res_ty, f, v, size)

            case LLVMVectorZipWith(type=res_ty, f=f, v1=v1, v2=v2, size=size):
                return self.to_ir_vector_zipwith(res_ty, f, v1, v2, size)

            case LLVMVectorCount(f=f, v=v, size=size):
                return self.to_ir_vector_count(f, v, size)

            case _:
                raise LLVMIRGenerationError(f"unsupported LLVM node {type(llvm_ast)}")

    def to_ir_literal(self, result_type: LLVMType, value: Any) -> ir.Value:
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

    def to_ir_variable(self, result_type: LLVMType, var_name: Name) -> ir.Value:
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

    def to_ir_if(self, result_type: LLVMType, cond: LLVMTerm, then_t: LLVMTerm, else_t: LLVMTerm) -> ir.Value | None:
        if self.builder is None:
            return None
        cond_val = self.to_ir(cond, False)

        with self.builder.if_else(cond_val) as (then_block, else_block):
            with then_block:
                then_val = self.to_ir(then_t, False)
                then_exit = self.builder.basic_block
            with else_block:
                else_val = self.to_ir(else_t, False)
                else_exit = self.builder.basic_block

        if isinstance(result_type, LLVMVoidType):
            return None

        phi = self.builder.phi(self.to_ir_type(result_type), name="if_res")
        phi.add_incoming(then_val if then_val is not None else ir.Constant(phi.type, 0), then_exit)
        phi.add_incoming(else_val if else_val is not None else ir.Constant(phi.type, 0), else_exit)
        return phi

    def to_ir_let(self, var_name: Name, var_value: LLVMTerm, body: LLVMTerm, is_top_level: bool) -> ir.Value | None:
        str_name = sanitize_name(var_name)
        if isinstance(var_value, LLVMFunction):
            var_value.name = var_name
            func = self.to_ir(var_value, False)
            self.env[str_name] = func
            return self.to_ir(body, is_top_level)

        val_gen = self.to_ir(var_value, False)
        old_val = self.env.get(str_name)
        self.env[str_name] = val_gen
        res = self.to_ir(body, is_top_level)

        if old_val is not None:
            self.env[str_name] = old_val
        else:
            del self.env[str_name]
        return res

    def to_ir_function(
        self, function_type: LLVMType, arg_names: list[Name], body: LLVMTerm, function_name: Name | None
    ) -> ir.Function:
        func_name = sanitize_name(function_name) if function_name else f"anon_func_{self.fn_count}"
        if not function_name:
            self.fn_count += 1

        func = self.module.globals.get(func_name) or ir.Function(
            self.module, self.to_ir_type(function_type), name=func_name
        )

        old_builder, old_env = self.builder, self.env.copy()
        self.env[func_name] = func

        self.builder = ir.IRBuilder(func.append_basic_block(name="entry"))
        for i, arg_name in enumerate(arg_names):
            str_arg_name = sanitize_name(arg_name)
            func.args[i].name = str_arg_name
            self.env[str_arg_name] = func.args[i]

        ret_val = self.to_ir(body, False)
        if isinstance(function_type, LLVMFunctionType) and isinstance(function_type.return_type, LLVMVoidType):
            self.builder.ret_void()
        else:
            self.builder.ret(ret_val)

        self.builder, self.env = old_builder, old_env
        return func

    def to_ir_call(self, target: LLVMTerm, args: list[LLVMTerm]) -> ir.Value | None:
        if self.builder is None:
            return None

        if isinstance(target, LLVMVar) and (target.name.name in BINARY_OPS or target.name.name in UNARY_OPS):
            return self.to_ir_operator(target.name.name, args)

        target_func = self.to_ir(target, False)
        arg_vals = [self.to_ir(arg, False) for arg in args]
        return self.builder.call(target_func, arg_vals) if target_func else None

    def to_ir_operator(self, op: str, args: list[LLVMTerm]) -> ir.Value | None:
        vals = [self.to_ir(arg, False) for arg in args]
        is_f = isinstance(vals[0].type, (ir.FloatType, ir.DoubleType))

        match op:
            case "+" if is_f:
                return self.builder.fadd(vals[0], vals[1])
            case "+":
                return self.builder.add(vals[0], vals[1])
            case "-" if is_f:
                return self.builder.fsub(vals[0], vals[1]) if len(vals) == 2 else self.builder.fneg(vals[0])
            case "-":
                return (
                    self.builder.sub(vals[0], vals[1])
                    if len(vals) == 2
                    else self.builder.sub(ir.Constant(vals[0].type, 0), vals[0])
                )
            case "*" if is_f:
                return self.builder.fmul(vals[0], vals[1])
            case "*":
                return self.builder.mul(vals[0], vals[1])
            case "/" if is_f:
                return self.builder.fdiv(vals[0], vals[1])
            case "/":
                return self.builder.sdiv(vals[0], vals[1])
            case "%" if is_f:
                return self.builder.frem(vals[0], vals[1])
            case "%":
                return self.builder.srem(vals[0], vals[1])
            case "==":
                return (
                    self.builder.fcmp_ordered("==", vals[0], vals[1])
                    if is_f
                    else self.builder.icmp_signed("==", vals[0], vals[1])
                )
            case "!=":
                return (
                    self.builder.fcmp_ordered("!=", vals[0], vals[1])
                    if is_f
                    else self.builder.icmp_signed("!=", vals[0], vals[1])
                )
            case "<":
                return (
                    self.builder.fcmp_ordered("<", vals[0], vals[1])
                    if is_f
                    else self.builder.icmp_signed("<", vals[0], vals[1])
                )
            case "<=":
                return (
                    self.builder.fcmp_ordered("<=", vals[0], vals[1])
                    if is_f
                    else self.builder.icmp_signed("<=", vals[0], vals[1])
                )
            case ">":
                return (
                    self.builder.fcmp_ordered(">", vals[0], vals[1])
                    if is_f
                    else self.builder.icmp_signed(">", vals[0], vals[1])
                )
            case ">=":
                return (
                    self.builder.fcmp_ordered(">=", vals[0], vals[1])
                    if is_f
                    else self.builder.icmp_signed(">=", vals[0], vals[1])
                )
            case "&&":
                return self.builder.and_(vals[0], vals[1])
            case "||":
                return self.builder.or_(vals[0], vals[1])
            case "!":
                return self.builder.not_(vals[0])
        return None

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

    def to_ir_vector_map(self, res_ty: LLVMType, f: LLVMTerm, v: LLVMTerm, size: LLVMTerm) -> ir.Value:
        f_val, v_val, size_val = self.to_ir(f, False), self.to_ir(v, False), self.to_ir(size, False)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._heap_alloc(res_base_ty, size_val)

        def body(idx):
            mapped_val = self.builder.call(f_val, [self.builder.load(self.builder.gep(v_val, [idx]))])
            if not isinstance(mapped_val.type, ir.VoidType):
                self.builder.store(mapped_val, self.builder.gep(new_v, [idx]))

        self.to_ir_loop(size_val, "map", body)
        return new_v

    def to_ir_vector_reduce(
        self, ty: LLVMType, f: LLVMTerm, initial: LLVMTerm, v: LLVMTerm, size: LLVMTerm
    ) -> ir.Value:
        f_val, init_val, v_val, size_val = (
            self.to_ir(f, False),
            self.to_ir(initial, False),
            self.to_ir(v, False),
            self.to_ir(size, False),
        )
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

        self.to_ir_loop(size_val, "reduce", body)
        return self.builder.load(acc_ptr)

    def to_ir_vector_imap(self, res_ty: LLVMType, f: LLVMTerm, v: LLVMTerm, size: LLVMTerm) -> ir.Value:
        f_val, v_val, size_val = self.to_ir(f, False), self.to_ir(v, False), self.to_ir(size, False)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._heap_alloc(res_base_ty, size_val)

        def body(idx):
            mapped_val = self.builder.call(f_val, [idx, self.builder.load(self.builder.gep(v_val, [idx]))])
            if not isinstance(mapped_val.type, ir.VoidType):
                self.builder.store(mapped_val, self.builder.gep(new_v, [idx]))

        self.to_ir_loop(size_val, "imap", body)
        return new_v

    def to_ir_vector_filter(self, res_ty: LLVMType, f: LLVMTerm, v: LLVMTerm, size: LLVMTerm) -> ir.Value:
        f_val, v_val, size_val = self.to_ir(f, False), self.to_ir(v, False), self.to_ir(size, False)
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._heap_alloc(res_base_ty, size_val)
        new_idx_ptr = self.builder.alloca(ir.IntType(32), name="filter_new_idx")
        self.builder.store(ir.Constant(ir.IntType(32), 0), new_idx_ptr)

        def body(idx):
            val = self.builder.load(self.builder.gep(v_val, [idx]))
            keep = self.builder.call(f_val, [val])
            with self.builder.if_then(keep):
                new_idx = self.builder.load(new_idx_ptr)
                self.builder.store(val, self.builder.gep(new_v, [new_idx]))
                self.builder.store(self.builder.add(new_idx, ir.Constant(ir.IntType(32), 1)), new_idx_ptr)

        self.to_ir_loop(size_val, "filter", body)
        return new_v

    def to_ir_vector_zipwith(
        self, res_ty: LLVMType, f: LLVMTerm, v1: LLVMTerm, v2: LLVMTerm, size: LLVMTerm
    ) -> ir.Value:
        f_val, v1_val, v2_val, size_val = (
            self.to_ir(f, False),
            self.to_ir(v1, False),
            self.to_ir(v2, False),
            self.to_ir(size, False),
        )
        res_base_ty = self.to_ir_type(res_ty.element_type if isinstance(res_ty, LLVMPointerType) else res_ty)
        if isinstance(res_base_ty, ir.VoidType):
            res_base_ty = ir.IntType(32)

        new_v = self._heap_alloc(res_base_ty, size_val)

        def body(idx):
            val1 = self.builder.load(self.builder.gep(v1_val, [idx]))
            val2 = self.builder.load(self.builder.gep(v2_val, [idx]))
            res = self.builder.call(f_val, [val1, val2])
            self.builder.store(res, self.builder.gep(new_v, [idx]))

        self.to_ir_loop(size_val, "zip", body)
        return new_v

    def to_ir_vector_count(self, f: LLVMTerm, v: LLVMTerm, size: LLVMTerm) -> ir.Value:
        f_val, v_val, size_val = self.to_ir(f, False), self.to_ir(v, False), self.to_ir(size, False)
        count_ptr = self.builder.alloca(ir.IntType(32), name="count_res")
        self.builder.store(ir.Constant(ir.IntType(32), 0), count_ptr)

        def body(idx):
            val = self.builder.load(self.builder.gep(v_val, [idx]))
            is_match = self.builder.call(f_val, [val])
            with self.builder.if_then(is_match):
                self.builder.store(
                    self.builder.add(self.builder.load(count_ptr), ir.Constant(ir.IntType(32), 1)), count_ptr
                )

        self.to_ir_loop(size_val, "count", body)
        return self.builder.load(count_ptr)
