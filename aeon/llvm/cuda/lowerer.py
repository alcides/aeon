from __future__ import annotations

from typing import Dict

from aeon.core.terms import Term
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMTerm,
    LLVMPointerType,
    LLVMAddressSpace,
    LLVMVoidType,
    LLVMCast,
)
from aeon.utils.name import Name


class CUDALLVMLowerer(CPULLVMLowerer):
    def __init__(self):
        super().__init__()

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
        if expected_type and isinstance(expected_type, LLVMPointerType):
            if expected_type.element_type != LLVMVoidType():
                expected_type = LLVMPointerType(expected_type.element_type, LLVMAddressSpace.GLOBAL)

        return super().lower(
            term,
            expected_type,
            type_env,
            env,
            allowed_func_calls,
            strict,
            in_vector_op,
        )

    def _get_vector_base_type(self, vector_type: LLVMType) -> LLVMType:
        base = super()._get_vector_base_type(vector_type)
        return base

    def _cast_if_needed(self, val: LLVMTerm, target_ty: LLVMType) -> LLVMTerm:
        if isinstance(val.type, LLVMPointerType) and isinstance(target_ty, LLVMPointerType):
            if val.type.address_space != target_ty.address_space:
                return LLVMCast(target_ty, val)
        return super()._cast_if_needed(val, target_ty)
