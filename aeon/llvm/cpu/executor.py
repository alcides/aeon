from __future__ import annotations

import ctypes
from typing import Any, List, Dict

import llvmlite.binding as llvm

from aeon.llvm.core import LLVMExecutionEngine, LLVMBackendError
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMIntType,
    LLVMFloatType,
    LLVMDoubleType,
    LLVMBoolType,
    LLVMCharType,
    LLVMVoidType,
    LLVMPointerType,
)


class LLVMExecutionError(LLVMBackendError):
    pass


class CPULLVMExecutionEngine(LLVMExecutionEngine):
    def __init__(self):
        self._init_llvm()
        self.target_machine = self._create_target_machine()
        self._keep_alive = []

    def _init_llvm(self):
        llvm.initialize_native_target()
        llvm.initialize_native_asmprinter()

    def _create_target_machine(self):
        target = llvm.Target.from_triple(llvm.get_process_triple())
        return target.create_target_machine()

    def _get_ctypes_type(self, ty: LLVMType) -> Any:
        match ty:
            case LLVMIntType(bits):
                types_map = {
                    1: ctypes.c_bool,
                    8: ctypes.c_int8,
                    16: ctypes.c_int16,
                    32: ctypes.c_int32,
                    64: ctypes.c_int64,
                }
                if bits in types_map:
                    return types_map[bits]
                raise LLVMExecutionError(f"unsupported integer width: {bits} bits")
            case LLVMBoolType():
                return ctypes.c_bool
            case LLVMFloatType():
                return ctypes.c_float
            case LLVMDoubleType():
                return ctypes.c_double
            case LLVMCharType():
                return ctypes.c_char
            case LLVMVoidType():
                return None
            case LLVMPointerType():
                return ctypes.c_void_p
            case _:
                raise LLVMExecutionError(f"unsupported LLVM type for execution: {ty}")

    def _flatten_list(self, val: Any) -> List[Any]:
        if not isinstance(val, (list, tuple)):
            return [val]
        res = []
        for item in val:
            if isinstance(item, (list, tuple)):
                res.extend(self._flatten_list(item))
            else:
                res.append(item)
        return res

    def _convert_to_ctypes(self, val: Any, ty: LLVMType) -> Any:
        if isinstance(ty, LLVMPointerType) and isinstance(val, list):
            flat_val = self._flatten_list(val)
            base_ty = ty.element_type
            element_cty = self._get_ctypes_type(base_ty)
            processed_flat_val = [self._convert_to_ctypes(item, base_ty) for item in flat_val]
            array_type = element_cty * len(processed_flat_val)
            c_array = array_type(*processed_flat_val)
            self._keep_alive.append(c_array)
            return ctypes.cast(c_array, ctypes.c_void_p)

        if isinstance(ty, LLVMCharType) and isinstance(val, str):
            return ord(val)

        return val

    def _get_vector_impl(self, arg_types: List[LLVMType], ret_type: LLVMType) -> Dict[str, Any]:
        def vector_get(ptr: ctypes.c_void_p, idx: int) -> Any:
            el_ty = self._get_ctypes_type(ret_type)
            return ctypes.cast(ptr, ctypes.POINTER(el_ty))[idx]

        def vector_set(ptr: ctypes.c_void_p, idx: int, val: Any) -> ctypes.c_void_p:
            # val is already converted to the correct type by ctypes
            el_ty = self._get_ctypes_type(arg_types[2]) if len(arg_types) > 2 else ctypes.c_int32
            ctypes.cast(ptr, ctypes.POINTER(el_ty))[idx] = val
            return ptr

        def native_dummy(code: ctypes.c_char_p) -> ctypes.c_void_p:
            return ctypes.c_void_p(None)

        return {
            "Vector_get": vector_get,
            "Vector_set": vector_set,
            "native": native_dummy,
        }

    def execute(
        self,
        llvm_ir: str,
        func_name: str,
        args: List[Any],
        arg_types: List[LLVMType],
        ret_type: LLVMType,
        debug: bool = False,
    ) -> Any:
        self._keep_alive = []

        # We need the actual function type to register the correct callback types
        # But we can also register them with a generic signature if needed.
        # However, for Vector_get/set, we need the element type.
        
        vector_impls = self._get_vector_impl(arg_types, ret_type)
        # We don't register them as global symbols if they are specialized per call? 
        # Actually, the JIT needs to find them. If we have multiple calls with different types,
        # we might need different names or a generic implementation that uses the type info.
        # But here 'execute' is for a specific function.
        
        # For now, let's register them. If there are multiple Vector_gets, they will conflict.
        # A better way would be to let the lowerer emit the implementation if it's not provided by a library.
        
        # For 'native', it's always the same.
        llvm.add_symbol("native", ctypes.cast(ctypes.CFUNCTYPE(ctypes.c_void_p, ctypes.c_char_p)(vector_impls["native"]), ctypes.c_void_p).value)

        backing_mod = llvm.parse_assembly(llvm_ir)

        backing_mod.verify()
        with llvm.create_mcjit_compiler(backing_mod, self.target_machine) as engine:
            engine.finalize_object()
            func_ptr = engine.get_function_address(func_name)
            if not func_ptr:
                raise LLVMExecutionError(f"failed to find function address for {func_name}")

            ctypes_args = [self._get_ctypes_type(t) for t in arg_types]
            ctypes_ret = self._get_ctypes_type(ret_type) if not isinstance(ret_type, LLVMVoidType) else None

            cfunc = ctypes.CFUNCTYPE(ctypes_ret, *ctypes_args)(func_ptr)
            processed_args = [self._convert_to_ctypes(val, ty) for val, ty in zip(args, arg_types)]
            result = cfunc(*processed_args)

            if isinstance(ret_type, LLVMCharType):
                return chr(result)

            return result
