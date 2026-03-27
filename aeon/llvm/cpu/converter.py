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
    LLVMAbstraction,
    LLVMCall,
)
from aeon.llvm.utils import BINARY_OPS, UNARY_OPS


class LLVMIRGenerationError(LLVMBackendError):
    pass


class CPULLVMIRGenerator(LLVMIRGenerator):
    def __init__(self):
        self.module = ir.Module(name="aeon_cpu_module")
        self.setup_native_target()
        self.builder = None
        self.env = {}
        self.fn_count = 0

    def setup_native_target(self):
        llvm.initialize_native_target()
        llvm.initialize_native_asmprinter()

        target_triple = llvm.get_process_triple()
        self.module.triple = target_triple

        target = llvm.Target.from_triple(target_triple)
        target_machine = target.create_target_machine()
        self.module.data_layout = str(target_machine.target_data)

    def get_llvm_ir_type_from_llvm(self, ty: LLVMType) -> ir.Type:
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
                return ir.VoidType()
            case LLVMFunctionType(arg_types, return_type):
                ir_return_type = self.get_llvm_ir_type_from_llvm(return_type)
                ir_arg_types = [self.get_llvm_ir_type_from_llvm(arg) for arg in arg_types]
                return ir.FunctionType(ir_return_type, ir_arg_types)
            case LLVMPointerType(base, address_space):
                ir_base = self.get_llvm_ir_type_from_llvm(base)
                return ir.PointerType(ir_base, address_space.value)
            case LLVMArrayType(base, size):
                ir_base = self.get_llvm_ir_type_from_llvm(base)
                return ir.ArrayType(ir_base, size if size is not None else 0)
            case _:
                raise LLVMIRGenerationError(f"unsupported LLVM type {ty}")

    def generate_kernels(self, kernels: list[LLVMTerm]) -> str:
        for kernel_ast in kernels:
            self._generate(kernel_ast, is_top_level=True)
        return str(self.module)

    def _generate(self, llvm_ast: LLVMTerm, is_top_level: bool):
        match llvm_ast:
            case LLVMLiteral(type=ty, value=val):
                ir_type = self.get_llvm_ir_type_from_llvm(ty)
                match ty:
                    case LLVMBoolType():
                        return ir.Constant(ir.IntType(1), 1 if val else 0)
                    case LLVMIntType(bits):
                        return ir.Constant(ir.IntType(bits), int(val))
                    case LLVMFloatType() | LLVMDoubleType():
                        return ir.Constant(ir_type, float(val))
                    case LLVMCharType():
                        return ir.Constant(ir.IntType(8), ord(val))

            case LLVMVar(type=ty, name=name):
                str_name = str(name)
                if str_name in self.env:
                    return self.env[str_name]
                if str_name in self.module.globals:
                    return self.module.globals[str_name]
                raise LLVMIRGenerationError(f"undefined variable {str_name}")

            case LLVMIf(type=ty, cond=cond, then_t=then_t, else_t=else_t):
                if self.builder is None:
                    return None
                cond_val = self._generate(cond, False)

                with self.builder.if_else(cond_val) as (then_block, else_block):
                    with then_block:
                        then_val = self._generate(then_t, False)
                        then_exit_block = self.builder.basic_block
                    with else_block:
                        else_val = self._generate(else_t, False)
                        else_exit_block = self.builder.basic_block

                if isinstance(ty, LLVMVoidType):
                    return None

                phi = self.builder.phi(self.get_llvm_ir_type_from_llvm(ty), name="if_result")
                phi.add_incoming(then_val, then_exit_block)
                phi.add_incoming(else_val, else_exit_block)
                return phi

            case LLVMLet(type=ty, var_name=name, var_value=val, body=body):
                str_name = str(name)

                if isinstance(val, LLVMAbstraction):
                    func_type = self.get_llvm_ir_type_from_llvm(val.type)
                    func = ir.Function(self.module, func_type, name=str_name)

                    old_val = self.env.get(str_name)
                    self.env[str_name] = func

                    old_builder = self.builder
                    old_env = self.env.copy()

                    block = func.append_basic_block(name="entry")
                    self.builder = ir.IRBuilder(block)

                    for i, arg_name in enumerate(val.arg_names):
                        str_arg_name = str(arg_name)
                        func.args[i].name = str_arg_name
                        self.env[str_arg_name] = func.args[i]

                    return_val = self._generate(val.body, False)

                    if isinstance(val.type.return_type, LLVMVoidType):
                        self.builder.ret_void()
                    else:
                        self.builder.ret(return_val)

                    self.builder = old_builder
                    self.env = old_env

                    if is_top_level:
                        return self._generate(body, True)

                    result = self._generate(body, False)

                    if old_val is not None:
                        self.env[str_name] = old_val
                    else:
                        del self.env[str_name]

                    return result

                if is_top_level:
                    val = self._generate(val, True)
                    val.name = str_name
                    self.env[str_name] = val
                    return self._generate(body, True)

                val = self._generate(val, False)
                old_val = self.env.get(str_name)

                val.name = str_name
                self.env[str_name] = val

                result = self._generate(body, False)

                if old_val is not None:
                    self.env[str_name] = old_val
                else:
                    del self.env[str_name]

                return result

            case LLVMAbstraction(type=ty, arg_names=names, arg_types=_, body=body):
                func_type = self.get_llvm_ir_type_from_llvm(ty)
                func_name = f"anon_func_{self.fn_count}"
                self.fn_count += 1

                func = ir.Function(self.module, func_type, name=func_name)

                old_builder = self.builder
                old_env = self.env.copy()

                block = func.append_basic_block(name="entry")
                self.builder = ir.IRBuilder(block)

                for i, arg_name in enumerate(names):
                    str_arg_name = str(arg_name)
                    func.args[i].name = str_arg_name
                    self.env[str_arg_name] = func.args[i]

                return_val = self._generate(body, False)

                match ty:
                    case LLVMVoidType():
                        self.builder.ret_void()
                    case _:
                        self.builder.ret(return_val)

                self.builder = old_builder
                self.env = old_env

                return func

            case LLVMCall(type=_, target=target, args=args):
                if self.builder is None:
                    return None
                if isinstance(target, LLVMVar) and (target.name.name in BINARY_OPS or target.name.name in UNARY_OPS):
                    op = target.name.name
                    arg_vals = [self._generate(arg, False) for arg in args]
                    arg_type = args[0].type

                    is_float = isinstance(arg_type, (LLVMFloatType, LLVMDoubleType))

                    if len(arg_vals) == 2 and op in BINARY_OPS:
                        match op:
                            case "+":
                                return (
                                    self.builder.fadd(arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.add(arg_vals[0], arg_vals[1])
                                )
                            case "-":
                                return (
                                    self.builder.fsub(arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.sub(arg_vals[0], arg_vals[1])
                                )
                            case "*":
                                return (
                                    self.builder.fmul(arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.mul(arg_vals[0], arg_vals[1])
                                )
                            case "/":
                                return (
                                    self.builder.fdiv(arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.sdiv(arg_vals[0], arg_vals[1])
                                )
                            case "%":
                                return (
                                    self.builder.frem(arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.srem(arg_vals[0], arg_vals[1])
                                )
                            case "==":
                                return (
                                    self.builder.fcmp_ordered("==", arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.icmp_signed("==", arg_vals[0], arg_vals[1])
                                )
                            case "!=":
                                return (
                                    self.builder.fcmp_ordered("!=", arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.icmp_signed("!=", arg_vals[0], arg_vals[1])
                                )
                            case "<":
                                return (
                                    self.builder.fcmp_ordered("<", arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.icmp_signed("<", arg_vals[0], arg_vals[1])
                                )
                            case "<=":
                                return (
                                    self.builder.fcmp_ordered("<=", arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.icmp_signed("<=", arg_vals[0], arg_vals[1])
                                )
                            case ">":
                                return (
                                    self.builder.fcmp_ordered(">", arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.icmp_signed(">", arg_vals[0], arg_vals[1])
                                )
                            case ">=":
                                return (
                                    self.builder.fcmp_ordered(">=", arg_vals[0], arg_vals[1])
                                    if is_float
                                    else self.builder.icmp_signed(">=", arg_vals[0], arg_vals[1])
                                )
                            case "&&":
                                return self.builder.and_(arg_vals[0], arg_vals[1])
                            case "||":
                                return self.builder.or_(arg_vals[0], arg_vals[1])
                    elif len(arg_vals) == 1 and op in UNARY_OPS:
                        match op:
                            case "!":
                                return self.builder.not_(arg_vals[0])
                            case "-":
                                return self.builder.fneg(arg_vals[0]) if is_float else self.builder.neg(arg_vals[0])

                target_func = self._generate(target, False)
                arg_vals = [self._generate(arg, False) for arg in args]
                return self.builder.call(target_func, arg_vals)

            case _:
                raise LLVMIRGenerationError(f"unsupported LLVM type {type(llvm_ast)}")
