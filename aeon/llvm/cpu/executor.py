from __future__ import annotations

import ctypes
from typing import Any, List, Dict

import llvmlite.binding as llvm

from aeon.llvm.core import LLVMExecutionEngine, LLVMBackendError
from aeon.llvm.optimization import optimize_module
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
    def __init__(self, opt_level: int = 3):
        self._init_llvm()
        self.target_machine = self._create_target_machine()
        # Cache before any PassBuilder run: accessing target_data afterwards can SEGV in llvmlite.
        self._data_layout = str(self.target_machine.target_data)
        self._keep_alive: list[Any] = []
        self.opt_level = opt_level
        # Persist MCJIT so ADT/buffer pointers remain valid across host calls
        # into the same compiled module.
        self._engine: Any = None
        self._engine_ir: str | None = None
        self._jit_tm: Any = None

    def _init_llvm(self):
        llvm.initialize_native_target()
        llvm.initialize_native_asmprinter()

    def _create_target_machine(self):
        target = llvm.Target.from_triple(llvm.get_process_triple())
        return target.create_target_machine()

    def _ensure_engine(self, llvm_ir: str) -> Any:
        if self._engine is not None and self._engine_ir == llvm_ir:
            return self._engine

        if self._engine is not None:
            self._engine.close()
            self._engine = None

        libc = ctypes.CDLL(None)
        llvm.add_symbol("malloc", ctypes.cast(libc.malloc, ctypes.c_void_p).value)
        llvm.add_symbol("free", ctypes.cast(libc.free, ctypes.c_void_p).value)

        backing_mod = llvm.parse_assembly(llvm_ir)
        backing_mod.verify()
        opt_tm = self._create_target_machine()
        optimize_module(backing_mod, opt_tm, self.opt_level)
        backing_mod.data_layout = self._data_layout
        self._jit_tm = self._create_target_machine()
        self._engine = llvm.create_mcjit_compiler(backing_mod, self._jit_tm)
        self._engine.finalize_object()
        self._engine_ir = llvm_ir
        return self._engine

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

    def _coerce_arg(self, val: Any, ty: LLVMType) -> Any:
        # Prelude ``/`` on Int uses Python true division; host-side Int args may arrive as float.
        if isinstance(ty, LLVMIntType) and isinstance(val, float):
            return int(val)
        return val

    def _convert_to_ctypes(self, val: Any, ty: LLVMType) -> Any:
        if isinstance(ty, LLVMPointerType) and isinstance(val, list):
            flat_val = self._flatten_list(val)
            base_ty = ty.element_type
            element_cty = self._get_ctypes_type(base_ty)
            processed_flat_val = [
                self._convert_to_ctypes(self._coerce_arg(item, base_ty), base_ty) for item in flat_val
            ]
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
    ) -> Any:
        self._keep_alive = []
        vector_impls = self._get_vector_impl(arg_types, ret_type)
        llvm.add_symbol(
            "native",
            ctypes.cast(
                ctypes.CFUNCTYPE(ctypes.c_void_p, ctypes.c_char_p)(vector_impls["native"]), ctypes.c_void_p
            ).value,
        )

        engine = self._ensure_engine(llvm_ir)
        func_ptr = engine.get_function_address(func_name)
        if not func_ptr:
            raise LLVMExecutionError(f"failed to find function address for {func_name}")

        ctypes_args = [self._get_ctypes_type(t) for t in arg_types]
        ctypes_ret = self._get_ctypes_type(ret_type) if not isinstance(ret_type, LLVMVoidType) else None

        cfunc = ctypes.CFUNCTYPE(ctypes_ret, *ctypes_args)(func_ptr)
        processed_args = [
            self._convert_to_ctypes(self._coerce_arg(val, ty), ty) for val, ty in zip(args, arg_types)
        ]
        result = cfunc(*processed_args)

        if isinstance(ret_type, LLVMCharType):
            return chr(result)

        # Reconstruct Python lists for Array-returning kernels.
        # ADT pointers (i8*) are opaque handles — do not treat them as arrays.
        if (
            isinstance(ret_type, LLVMPointerType)
            and result is not None
            and not isinstance(ret_type.element_type, LLVMCharType)
        ):
            size = self._infer_result_size(args, arg_types)
            if size is not None and size >= 0:
                el_cty = self._get_ctypes_type(ret_type.element_type)
                ptr = ctypes.cast(result, ctypes.POINTER(el_cty))
                return [ptr[i] for i in range(size)]

        return result

    def _infer_result_size(self, args: List[Any], arg_types: List[LLVMType]) -> int | None:
        """Best-effort size for pointer results: last Int arg, else len of first list."""
        for val, ty in zip(reversed(args), reversed(arg_types)):
            if isinstance(ty, LLVMIntType) and isinstance(val, int):
                return val
        for val in args:
            if isinstance(val, list):
                return len(val)
        return None
