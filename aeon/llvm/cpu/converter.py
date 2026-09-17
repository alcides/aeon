from __future__ import annotations

import re

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
    LLVMFoldN,
    VECTOR_OPERATIONS,
    LLVMCast,
    LLVMRefinedValue,
    LLVMADTConstruct,
    LLVMADTEliminate,
)
from aeon.llvm.refinements import emit_predicate, integer_range, parameter_ranges
from aeon.llvm.safety import refinement_arithmetic_is_safe
from aeon.llvm.utils import BINARY_OPS, UNARY_OPS, sanitize_name
from aeon.utils.name import Name
from typing import Dict, Any, Callable


class LLVMIRGenerationError(LLVMBackendError):
    pass


class CPULLVMIRGenerator(LLVMIRGenerator, LLVMVisitor):
    def __init__(self, use_refinements: bool = True):
        llvm.initialize_native_target()
        llvm.initialize_native_asmprinter()

        self.module = ir.Module(name="aeon_cpu_module")
        self.module.triple = llvm.get_process_triple()
        target = llvm.Target.from_triple(self.module.triple)
        target_machine = target.create_target_machine()
        self.module.data_layout = str(target_machine.target_data)
        self.target_data = target_machine.target_data

        self.builder: Any = None
        self.env: dict[str, Any] = {}
        self.fn_count = 0
        self._is_top_level = False
        self.use_refinements = use_refinements
        self.refinements_enabled = use_refinements
        self.refinement_env: dict[Name, ir.Value] = {}
        self.parameter_ranges: dict[str, list[tuple[int, int] | None]] = {}

    @staticmethod
    def _add_parameter_attributes(argument: ir.Argument) -> None:
        """Mark values crossing an Aeon function boundary as fully defined.

        Aeon has no source-level ``undef`` or poison values. ``noundef`` is
        therefore justified for every lowered parameter. Pointer-specific
        claims such as ``nonnull`` or ``dereferenceable`` require explicit
        contracts and are deliberately left out.
        """
        argument.add_attribute("noundef")

    def _assume(self, predicate, extra=None):
        if not self.refinements_enabled:
            return
        condition = emit_predicate(self.builder, predicate, self.refinement_env | (extra or {}))
        if condition is not None:
            assume = self.module.declare_intrinsic("llvm.assume")
            self.builder.call(assume, [condition])

    def visit_refinement(self, node: LLVMRefinedValue):
        value = node.value.accept(self)
        if not self.refinements_enabled or value is None:
            return value
        ref = node.refinement
        # Only annotate the instruction produced here, never a load reused
        # through a variable: the refinement might hold only in this branch.
        if isinstance(node.value, (LLVMLoad, LLVMCall)) and isinstance(value.type, ir.IntType):
            bounds = integer_range(ref.refinement, ref.name, value.type.width)
            if bounds is not None and getattr(value, "opname", None) in {"load", "call"}:
                value.set_metadata(
                    "range",
                    self.module.add_metadata([ir.Constant(value.type, n % (1 << value.type.width)) for n in bounds]),
                )
        if not node.range_only:
            self._assume(ref.refinement, {ref.name: value})
        return value

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
        self.refinements_enabled = self.use_refinements and refinement_arithmetic_is_safe(definitions)
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
        return self._attach_parameter_ranges(str(self.module))

    def _attach_parameter_ranges(self, code: str) -> str:
        """Add LLVM's type-level range attributes unavailable in llvmlite's API."""
        if not self.refinements_enabled:
            return code
        for function_name, ranges in self.parameter_ranges.items():
            for index, bounds in enumerate(ranges):
                if bounds is None:
                    continue
                lo, hi = bounds
                width = 32

                def signed_endpoint(value: int) -> int:
                    limit = 1 << (width - 1)
                    return value - (1 << width) if value >= limit else value

                match = re.search(rf'(define [^\n]*@"{re.escape(function_name)}"\([^\n]*\))', code)
                if match is None:
                    continue
                signature = match.group(1)
                args = re.findall(r'i(\d+) noundef %"[^\"]+"', signature)
                if index >= len(args) or int(args[index]) != width:
                    continue
                matches = list(re.finditer(r'i32 noundef %"[^\"]+"', signature))
                if index >= len(matches):
                    continue
                old = matches[index]
                start = match.start(1) + old.start()
                argument_name = old.group(0).split("noundef ", 1)[1]
                replacement = f"i32 range(i32 {signed_endpoint(lo)}, {signed_endpoint(hi)}) noundef {argument_name}"
                code = code[:start] + replacement + code[start + len(old.group(0)) :]
        return code

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
        if base_name == "PI" or base_name.endswith("_PI"):
            return ir.Constant(ir.DoubleType(), 3.141592653589793)

        builtin_map = {
            "pow": "pow",
            "powf": "pow",
            "sqrt": "sqrt",
            "sqrtf": "sqrt",
            "sin": "sin",
            "cos": "cos",
            "exp": "exp",
            "log": "log",
            "absf": "fabs",
            "minf": "fmin",
            "maxf": "fmax",
            "cbrt": "cbrt",
            "expm1": "expm1",
            "exp2": "exp2",
            "log10": "log10",
            "log2": "log2",
            "log1p": "log1p",
            "tan": "tan",
            "asin": "asin",
            "acos": "acos",
            "atan": "atan",
            "atan2": "atan2",
            "sinh": "sinh",
            "cosh": "cosh",
            "tanh": "tanh",
            "asinh": "asinh",
            "acosh": "acosh",
            "atanh": "atanh",
            "erf": "erf",
            "erfc": "erfc",
            "lgamma": "lgamma",
            "gamma": "tgamma",
            "remainder": "remainder",
            "fmod": "fmod",
            "hypot": "hypot",
            "copysign": "copysign",
            "fma": "fma",
        }

        name_parts = str_name.rsplit("_", 1)
        lookup_name = name_parts[0] if len(name_parts) > 1 and name_parts[1].isdigit() else str_name

        # Strip module prefix (e.g. "Math_powf" -> "powf") for builtin lookup
        if "_" in lookup_name and lookup_name not in builtin_map:
            bare = lookup_name.split("_", 1)[1]
            if bare in builtin_map:
                lookup_name = bare

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
                if then_val is not None and not isinstance(result_type, LLVMVoidType):
                    then_val = self._coerce_to_type(then_val, self.to_ir_type(result_type))
                then_exit = self.builder.basic_block
            with else_block:
                self._is_top_level = False
                else_val = else_t.accept(self)
                if else_val is not None and not isinstance(result_type, LLVMVoidType):
                    else_val = self._coerce_to_type(else_val, self.to_ir_type(result_type))
                else_exit = self.builder.basic_block

        if isinstance(result_type, LLVMVoidType):
            return None

        phi = self.builder.phi(self.to_ir_type(result_type), name="if_res")
        left = then_val if then_val is not None else ir.Constant(phi.type, 0)
        right = else_val if else_val is not None else ir.Constant(phi.type, 0)
        phi.add_incoming(left, then_exit)
        phi.add_incoming(right, else_exit)
        return phi

    def visit_let(self, node: LLVMLet) -> ir.Value | None:
        var_name, var_value, body, is_top_level = node.var_name, node.var_value, node.body, self._is_top_level
        str_name = sanitize_name(var_name)
        if isinstance(var_value, LLVMFunction):
            var_value.name = var_name
            self._is_top_level = False
            func = var_value.accept(self)
            self.env[str_name] = func
            self._is_top_level = is_top_level
            return body.accept(self)

        self._is_top_level = False
        val_gen = var_value.accept(self)
        old_val = self.env.get(str_name)
        old_refinement_value = self.refinement_env.get(var_name)
        self.env[str_name] = val_gen
        self.refinement_env[var_name] = val_gen
        self._is_top_level = is_top_level
        res = body.accept(self)

        if old_val is not None:
            self.env[str_name] = old_val
        else:
            del self.env[str_name]
        if old_refinement_value is None:
            self.refinement_env.pop(var_name, None)
        else:
            self.refinement_env[var_name] = old_refinement_value
        return res

    def visit_function(self, node: LLVMFunction) -> ir.Function:
        function_type, arg_names, body, function_name = node.type, node.arg_names, node.body, node.name
        func_name = sanitize_name(function_name) if function_name else f"anon_func_{self.fn_count}"
        if not function_name:
            self.fn_count += 1

        func = self.module.globals.get(func_name) or ir.Function(
            self.module, self.to_ir_type(function_type), name=func_name
        )
        if func.blocks:
            return func

        old_builder, old_env = self.builder, self.env.copy()
        old_refinement_env = self.refinement_env
        self.refinement_env = {}
        self.env[func_name] = func

        self.builder = ir.IRBuilder(func.append_basic_block(name="entry"))
        for i, arg_name in enumerate(arg_names):
            str_arg_name = sanitize_name(arg_name)
            func.args[i].name = str_arg_name
            self._add_parameter_attributes(func.args[i])
            self.env[str_arg_name] = func.args[i]
            self.refinement_env[arg_name] = func.args[i]
        if isinstance(function_type, LLVMFunctionType):
            self.parameter_ranges[func_name] = parameter_ranges(function_type.source_type, arg_names)

        for predicate in node.refinements:
            self._assume(predicate)

        self._is_top_level = False
        ret_val = body.accept(self)
        if isinstance(function_type, LLVMFunctionType) and isinstance(function_type.return_type, LLVMVoidType):
            self.builder.ret_void()
        else:
            expected_ir = self.to_ir_type(function_type.return_type) if isinstance(function_type, LLVMFunctionType) else ret_val.type
            self.builder.ret(self._coerce_to_type(ret_val, expected_ir))

        self.builder, self.env = old_builder, old_env
        self.refinement_env = old_refinement_env
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
            coerced = [
                self._coerce_to_type(v, t) for v, t in zip(arg_vals, target_func.function_type.args)
            ]
            return self.builder.call(target_func, coerced)
        return self.builder.call(target_func, arg_vals)

    def to_ir_operator(self, op: str, args: list[LLVMTerm]) -> ir.Value | None:
        self._is_top_level = False
        vals = [arg.accept(self) for arg in args]
        if any(v is None for v in vals):
            return None
        is_f = isinstance(vals[0].type, (ir.FloatType, ir.DoubleType))

        def as_i64(val: ir.Value) -> ir.Value:
            if isinstance(val.type, ir.IntType) and val.type.width < 64:
                return self.builder.sext(val, ir.IntType(64))
            return val

        def int_binop(binop):
            # Keep intermediate Int arithmetic in i64 so expressions like the
            # LCG multiply-add match Python's unbounded Int before ``%``.
            return binop(as_i64(vals[0]), as_i64(vals[1]))

        match op:
            case "+" if is_f:
                return self.builder.fadd(vals[0], vals[1])
            case "+":
                return int_binop(self.builder.add)
            case "-" if is_f:
                return self.builder.fsub(vals[0], vals[1]) if len(vals) == 2 else self.builder.fneg(vals[0])
            case "-":
                if len(vals) == 2:
                    return int_binop(self.builder.sub)
                zero = ir.Constant(ir.IntType(64), 0)
                return self.builder.sub(zero, as_i64(vals[0]))
            case "*" if is_f:
                return self.builder.fmul(vals[0], vals[1])
            case "*":
                return int_binop(self.builder.mul)
            case "/" if is_f:
                return self.builder.fdiv(vals[0], vals[1])
            case "/":
                return int_binop(self.builder.sdiv)
            case "%" if is_f:
                return self.builder.frem(vals[0], vals[1])
            case "%":
                return int_binop(self.builder.srem)
            case "==":
                if is_f:
                    return self.builder.fcmp_ordered("==", vals[0], vals[1])
                a, b = as_i64(vals[0]), as_i64(vals[1])
                return self.builder.icmp_signed("==", a, b)
            case "!=":
                if is_f:
                    return self.builder.fcmp_ordered("!=", vals[0], vals[1])
                a, b = as_i64(vals[0]), as_i64(vals[1])
                return self.builder.icmp_signed("!=", a, b)
            case "<":
                if is_f:
                    return self.builder.fcmp_ordered("<", vals[0], vals[1])
                a, b = as_i64(vals[0]), as_i64(vals[1])
                return self.builder.icmp_signed("<", a, b)
            case "<=":
                if is_f:
                    return self.builder.fcmp_ordered("<=", vals[0], vals[1])
                a, b = as_i64(vals[0]), as_i64(vals[1])
                return self.builder.icmp_signed("<=", a, b)
            case ">":
                if is_f:
                    return self.builder.fcmp_ordered(">", vals[0], vals[1])
                a, b = as_i64(vals[0]), as_i64(vals[1])
                return self.builder.icmp_signed(">", a, b)
            case ">=":
                if is_f:
                    return self.builder.fcmp_ordered(">=", vals[0], vals[1])
                a, b = as_i64(vals[0]), as_i64(vals[1])
                return self.builder.icmp_signed(">=", a, b)
            case "&&":
                return self.builder.and_(vals[0], vals[1])
            case "||":
                return self.builder.or_(vals[0], vals[1])
            case "!":
                return self.builder.not_(vals[0])
        return None

    def visit_cast(self, node: LLVMCast) -> ir.Value:
        val, ty = node.val, node.type
        self._is_top_level = False
        v_val = val.accept(self)
        target_ty = self.to_ir_type(ty)
        if v_val.type == target_ty:
            return v_val
        if isinstance(v_val.type, ir.IntType) and isinstance(target_ty, ir.IntType):
            if v_val.type.width < target_ty.width:
                return self.builder.sext(v_val, target_ty)
            return self.builder.trunc(v_val, target_ty)
        if isinstance(v_val.type, ir.IntType) and isinstance(target_ty, (ir.FloatType, ir.DoubleType)):
            return self.builder.sitofp(v_val, target_ty)
        if isinstance(v_val.type, (ir.FloatType, ir.DoubleType)) and isinstance(target_ty, ir.IntType):
            return self.builder.fptosi(v_val, target_ty)
        if isinstance(v_val.type, ir.FloatType) and isinstance(target_ty, ir.DoubleType):
            return self.builder.fpext(v_val, target_ty)
        if isinstance(v_val.type, ir.DoubleType) and isinstance(target_ty, ir.FloatType):
            return self.builder.fptrunc(v_val, target_ty)
        return self.builder.bitcast(v_val, target_ty)

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
        return p_val if isinstance(v_val.type, ir.VoidType) else self.builder.store(v_val, p_val)

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

        self.to_ir_loop(size_val, "map", body)
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

        self.to_ir_loop(size_val, "reduce", body)
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

        self.to_ir_loop(size_val, "imap", body)
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
            with self.builder.if_then(keep):
                new_idx = self.builder.load(new_idx_ptr)
                self.builder.store(val, self.builder.gep(new_v, [new_idx]))
                self.builder.store(self.builder.add(new_idx, ir.Constant(ir.IntType(32), 1)), new_idx_ptr)

        self.to_ir_loop(size_val, "filter", body)
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

        self.to_ir_loop(size_val, "zip", body)
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
            with self.builder.if_then(is_match):
                self.builder.store(
                    self.builder.add(self.builder.load(count_ptr), ir.Constant(ir.IntType(32), 1)), count_ptr
                )

        self.to_ir_loop(size_val, "count", body)
        return self.builder.load(count_ptr)

    def visit_fold_n(self, node: LLVMFoldN) -> ir.Value:
        ty, f, initial, size = node.type, node.f, node.initial, node.size
        self._is_top_level = False
        f_val, init_val, size_val = f.accept(self), initial.accept(self), size.accept(self)
        acc_ty = self.to_ir_type(ty)
        if isinstance(acc_ty, ir.VoidType):
            acc_ty = ir.IntType(32)

        acc_ptr = self.builder.alloca(acc_ty, name="fold_n_acc")
        if init_val and not isinstance(init_val.type, ir.VoidType):
            self.builder.store(init_val, acc_ptr)

        def body(idx):
            new_acc = self.builder.call(f_val, [self.builder.load(acc_ptr), idx])
            if not isinstance(new_acc.type, ir.VoidType):
                self.builder.store(new_acc, acc_ptr)

        self.to_ir_loop(size_val, "fold_n", body)
        return self.builder.load(acc_ptr)

    def _coerce_int(self, val: ir.Value, bits: int = 32) -> ir.Value:
        """Truncate/extend integer values to ``bits`` (Aeon ``Int`` is i32 at ABI)."""
        if not isinstance(val.type, ir.IntType):
            return val
        if val.type.width == bits:
            return val
        if val.type.width > bits:
            return self.builder.trunc(val, ir.IntType(bits))
        return self.builder.sext(val, ir.IntType(bits))

    def _coerce_to_type(self, val: ir.Value, ir_ty: ir.Type) -> ir.Value:
        if isinstance(ir_ty, ir.IntType) and isinstance(val.type, ir.IntType):
            return self._coerce_int(val, ir_ty.width)
        return val

    def _i8_ptr_type(self) -> ir.PointerType:
        return ir.PointerType(ir.IntType(8))

    def _pack_field_i64(self, val: ir.Value) -> ir.Value:
        i64 = ir.IntType(64)
        if isinstance(val.type, ir.PointerType):
            return self.builder.ptrtoint(val, i64)
        if isinstance(val.type, ir.IntType):
            # Normalize Aeon Int (possibly widened i64 intermediate) into a 32-bit
            # payload, then store in the i64 slot.
            narrowed = self._coerce_int(val, 32)
            if narrowed.type.width < 64:
                return self.builder.sext(narrowed, i64) if narrowed.type.width > 1 else self.builder.zext(narrowed, i64)
            return narrowed
        if isinstance(val.type, ir.FloatType):
            return self.builder.zext(self.builder.bitcast(val, ir.IntType(32)), i64)
        if isinstance(val.type, ir.DoubleType):
            return self.builder.bitcast(val, i64)
        raise LLVMIRGenerationError(f"cannot pack field of type {val.type} into ADT slot")



    def _unpack_field_i64(self, packed: ir.Value, ty: LLVMType) -> ir.Value:
        ir_ty = self.to_ir_type(ty)
        if isinstance(ir_ty, ir.PointerType):
            return self.builder.inttoptr(packed, ir_ty)
        if isinstance(ir_ty, ir.IntType):
            if ir_ty.width < 64:
                return self.builder.trunc(packed, ir_ty)
            return packed
        if isinstance(ir_ty, ir.FloatType):
            return self.builder.bitcast(self.builder.trunc(packed, ir.IntType(32)), ir_ty)
        if isinstance(ir_ty, ir.DoubleType):
            return self.builder.bitcast(packed, ir_ty)
        raise LLVMIRGenerationError(f"cannot unpack ADT field to type {ty}")

    def _adt_field_types(self, case: LLVMTerm, arity: int, declared: list[LLVMType] | None = None) -> list[LLVMType]:
        if declared and len(declared) >= arity:
            return list(declared)[:arity]
        if isinstance(case, LLVMFunction):
            return list(case.arg_types)[:arity]
        if isinstance(case.type, LLVMFunctionType):
            return list(case.type.arg_types)[:arity]
        return [LLVMIntType(32)] * arity

    def visit_adt_construct(self, node: LLVMADTConstruct) -> ir.Value:
        if self.builder is None:
            raise LLVMIRGenerationError("ADT construct outside of a function body")
        i8ptr = self._i8_ptr_type()
        if node.nullary_as_null:
            return ir.Constant(i8ptr, None)

        fields = [f.accept(self) for f in node.fields]
        # Layout: [i32 tag][i32 pad][i64 field]*
        nbytes = 8 + 8 * len(fields)
        size = ir.Constant(ir.IntType(64), nbytes)
        malloc_ty = ir.FunctionType(i8ptr, [ir.IntType(64)])
        malloc_func = self.module.globals.get("malloc")
        if not malloc_func:
            malloc_func = ir.Function(self.module, malloc_ty, name="malloc")
        raw = self.builder.call(malloc_func, [size], name=f"adt_{node.ctor_name}")

        tag_ptr = self.builder.bitcast(raw, ir.PointerType(ir.IntType(32)))
        self.builder.store(ir.Constant(ir.IntType(32), node.tag), tag_ptr)

        for i, field_val in enumerate(fields):
            off = self.builder.gep(raw, [ir.Constant(ir.IntType(32), 8 + 8 * i)])
            slot = self.builder.bitcast(off, ir.PointerType(ir.IntType(64)))
            self.builder.store(self._pack_field_i64(field_val), slot)
        return raw

    def visit_adt_eliminate(self, node: LLVMADTEliminate) -> ir.Value:
        if self.builder is None:
            raise LLVMIRGenerationError("ADT eliminate outside of a function body")

        scrut = node.scrutinee.accept(self)
        result_ty = self.to_ir_type(node.type)
        i8ptr = self._i8_ptr_type()
        parent = self.builder.function
        merge = parent.append_basic_block(name=f"{node.type_name}_merge")
        phi_incoming: list[tuple[ir.Value, ir.Block]] = []

        use_null = bool(node.case_arities) and node.case_arities[0] == 0

        def emit_case(idx: int) -> None:
            case = node.cases[idx]
            arity = node.case_arities[idx]
            declared = node.case_field_types[idx] if idx < len(node.case_field_types) else []
            if arity == 0:
                val = case.accept(self)
            elif isinstance(case, LLVMFunction):
                # Inline the handler in this function so free variables from the
                # enclosing Aeon scope remain visible (nested LLVM functions
                # cannot capture outer SSA values).
                field_tys = self._adt_field_types(case, arity, declared)
                old_env = {sanitize_name(n): self.env.get(sanitize_name(n)) for n in case.arg_names}
                for i, (name, fty) in enumerate(zip(case.arg_names, field_tys)):
                    off = self.builder.gep(scrut, [ir.Constant(ir.IntType(32), 8 + 8 * i)])
                    slot = self.builder.bitcast(off, ir.PointerType(ir.IntType(64)))
                    packed = self.builder.load(slot)
                    self.env[sanitize_name(name)] = self._unpack_field_i64(packed, fty)
                val = case.body.accept(self)
                for name, prev in old_env.items():
                    if prev is None:
                        self.env.pop(name, None)
                    else:
                        self.env[name] = prev
            else:
                field_tys = self._adt_field_types(case, arity, declared)
                extracted: list[ir.Value] = []
                for i, fty in enumerate(field_tys):
                    off = self.builder.gep(scrut, [ir.Constant(ir.IntType(32), 8 + 8 * i)])
                    slot = self.builder.bitcast(off, ir.PointerType(ir.IntType(64)))
                    packed = self.builder.load(slot)
                    extracted.append(self._unpack_field_i64(packed, fty))
                handler = case.accept(self)
                val = self.builder.call(handler, extracted)
            if isinstance(result_ty, ir.VoidType):
                self.builder.branch(merge)
            else:
                coerced = self._coerce_to_type(val, result_ty)
                phi_incoming.append((coerced, self.builder.block))
                self.builder.branch(merge)

        if use_null:
            null_bb = parent.append_basic_block(name=f"{node.type_name}_null")
            tagged_bb = parent.append_basic_block(name=f"{node.type_name}_tagged")
            is_null = self.builder.icmp_unsigned("==", scrut, ir.Constant(i8ptr, None))
            self.builder.cbranch(is_null, null_bb, tagged_bb)

            self.builder.position_at_start(null_bb)
            emit_case(0)

            self.builder.position_at_start(tagged_bb)
            tag_ptr = self.builder.bitcast(scrut, ir.PointerType(ir.IntType(32)))
            tag = self.builder.load(tag_ptr)
            default = parent.append_basic_block(name=f"{node.type_name}_default")
            switch = self.builder.switch(tag, default)
            for idx in range(1, len(node.cases)):
                bb = parent.append_basic_block(name=f"{node.type_name}_case{idx}")
                switch.add_case(ir.Constant(ir.IntType(32), idx), bb)
                self.builder.position_at_start(bb)
                emit_case(idx)
            self.builder.position_at_start(default)
            if isinstance(result_ty, ir.VoidType):
                self.builder.branch(merge)
            else:
                zero = ir.Constant(result_ty, None if isinstance(result_ty, ir.PointerType) else 0)
                phi_incoming.append((zero, default))
                self.builder.branch(merge)
        else:
            tag_ptr = self.builder.bitcast(scrut, ir.PointerType(ir.IntType(32)))
            tag = self.builder.load(tag_ptr)
            default = parent.append_basic_block(name=f"{node.type_name}_default")
            switch = self.builder.switch(tag, default)
            for idx in range(len(node.cases)):
                bb = parent.append_basic_block(name=f"{node.type_name}_case{idx}")
                switch.add_case(ir.Constant(ir.IntType(32), idx), bb)
                self.builder.position_at_start(bb)
                emit_case(idx)
            self.builder.position_at_start(default)
            if isinstance(result_ty, ir.VoidType):
                self.builder.branch(merge)
            else:
                zero = ir.Constant(result_ty, None if isinstance(result_ty, ir.PointerType) else 0)
                phi_incoming.append((zero, default))
                self.builder.branch(merge)

        self.builder.position_at_start(merge)
        if isinstance(result_ty, ir.VoidType):
            return None
        phi = self.builder.phi(result_ty, name=f"{node.type_name}_res")
        for val, block in phi_incoming:
            phi.add_incoming(val, block)
        return phi
