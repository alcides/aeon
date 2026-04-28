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


class LLVMVector:
    def __init__(self, addr, element_cty):
        self.addr = addr
        self.element_cty = element_cty

    def __getitem__(self, i):
        if i >= len(self):
            raise IndexError("index out of range")
        res = ctypes.cast(self.addr, ctypes.POINTER(self.element_cty))[i]
        if self.element_cty == ctypes.c_char:
            return chr(res)
        return res

    def __len__(self):
        size_ptr = ctypes.cast(ctypes.c_void_p(self.addr - 8), ctypes.POINTER(ctypes.c_int32))
        return size_ptr[0]

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]

    def __repr__(self):
        return f"LLVMVector(addr={self.addr}, size={len(self)})"


class CPULLVMExecutionEngine(LLVMExecutionEngine):
    def __init__(self):
        self._init_llvm()
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
        if isinstance(ty, LLVMPointerType):
            if hasattr(val, "__cuda_array_interface__"):  # CuPy
                return ctypes.c_void_p(val.data.ptr)
            if hasattr(val, "ctypes"):  # NumPy
                return ctypes.c_void_p(val.ctypes.data)

        if isinstance(ty, LLVMPointerType) and isinstance(val, list):
            flat_val = self._flatten_list(val)
            base_ty = ty.element_type
            element_cty = self._get_ctypes_type(base_ty)
            processed_flat_val = [self._convert_to_ctypes(item, base_ty) for item in flat_val]

            header_size = 8
            data_size = len(processed_flat_val) * ctypes.sizeof(element_cty)
            buffer = (ctypes.c_byte * (header_size + data_size))()

            size_ptr = ctypes.cast(buffer, ctypes.POINTER(ctypes.c_int32))
            size_ptr[0] = len(processed_flat_val)

            if processed_flat_val:
                data_ptr = ctypes.cast(ctypes.addressof(buffer) + header_size, ctypes.POINTER(element_cty))
                for i, v in enumerate(processed_flat_val):
                    data_ptr[i] = v

            self._keep_alive.append(buffer)
            return ctypes.cast(ctypes.addressof(buffer) + header_size, ctypes.c_void_p)

        if isinstance(ty, LLVMCharType) and isinstance(val, str):
            return ord(val)

        return val

    def _get_vector_impl(self, arg_types: List[LLVMType], ret_type: LLVMType) -> Dict[str, Any]:
        def vector_get(ptr: ctypes.c_void_p, idx: int) -> Any:
            el_ty = self._get_ctypes_type(ret_type)
            return ctypes.cast(ptr, ctypes.POINTER(el_ty))[idx]

        def vector_set(ptr: ctypes.c_void_p, idx: int, val: Any) -> ctypes.c_void_p:
            el_ty = self._get_ctypes_type(arg_types[2]) if len(arg_types) > 2 else ctypes.c_int32
            ctypes.cast(ptr, ctypes.POINTER(el_ty))[idx] = val
            return ptr

        def native_dummy(code: ctypes.c_char_p) -> ctypes.c_void_p:
            return ctypes.c_void_p(None)

        return {
            "get": vector_get,
            "set": vector_set,
            "native": native_dummy,
        }

    def execute(
        self,
        llvm_ir: str,
        func_name: str,
        args: List[Any],
        arg_types: List[LLVMType],
        ret_type: LLVMType,
        metadata: dict[str, Any] | None = None,
    ) -> Any:
        self._keep_alive = []
        metadata = metadata or {}
        opt_level = metadata.get("cpu_opt_level", 3)

        vector_impls = self._get_vector_impl(arg_types, ret_type)
        llvm.add_symbol(
            "native",
            ctypes.cast(
                ctypes.CFUNCTYPE(ctypes.c_void_p, ctypes.c_char_p)(vector_impls["native"]), ctypes.c_void_p
            ).value,
        )

        backing_mod = llvm.parse_assembly(llvm_ir)
        backing_mod.verify()

        pto = llvm.create_pipeline_tuning_options()
        pto.opt_level = opt_level
        pb = llvm.create_pass_builder(self.target_machine, pto)
        pm = llvm.create_new_module_pass_manager()
        pb.populate_module_pass_manager(pm)
        pm.run(backing_mod, pb)

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

            if isinstance(ret_type, LLVMPointerType) and result is not None:
                element_cty = self._get_ctypes_type(ret_type.element_type)
                return LLVMVector(result, element_cty)

            return result
