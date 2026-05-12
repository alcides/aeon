from __future__ import annotations

from aeon.core.terms import Term
from aeon.llvm.constants import VectorOperation
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMTerm,
    LLVMPointerType,
    LLVMAddressSpace,
    LLVMVoidType,
    LLVMCast,
    LLVMFunctionType,
    LLVMVectorCount,
    LLVMInt,
    LLVMBool,
)
from aeon.utils.name import Name


class CUDALLVMLowerer(CPULLVMLowerer):
    def __init__(self):
        super().__init__()

    def lower(
        self,
        term: Term,
        expected_type: LLVMType | None = None,
        type_env: dict[Name, LLVMType] | None = None,
        env: dict[Name, LLVMTerm] | None = None,
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

    def _lower_vector_op(
        self,
        op: str,
        args: list[Term | LLVMTerm],
        expected: LLVMType | None,
        type_env: dict[Name, LLVMType],
        env: dict[Name, LLVMTerm],
        allowed: set[Name],
    ) -> LLVMTerm:
        if op == VectorOperation.COUNT:
            kernel_term, vector_term, size_term = args
            low_vec = self._lower_term(vector_term, None, type_env, env, allowed, in_vector_op=True)
            low_size = self._lower_term(size_term, LLVMInt, type_env, env, allowed, in_vector_op=True)
            element_type = self._get_vector_base_type(low_vec.type)
            vec_cast = self._cast_if_needed(low_vec, LLVMPointerType(element_type))
            kernel = self._lower_as_standalone(
                kernel_term,
                LLVMFunctionType([element_type], LLVMBool),
                type_env,
                env,
                allowed,
                True,
            )
            return LLVMVectorCount(LLVMInt, kernel, vec_cast, low_size)

        return super()._lower_vector_op(op, args, expected, type_env, env, allowed)

    def _cast_if_needed(self, val: LLVMTerm, target_ty: LLVMType) -> LLVMTerm:
        if isinstance(val.type, LLVMPointerType) and isinstance(target_ty, LLVMPointerType):
            if val.type.address_space != target_ty.address_space:
                return LLVMCast(target_ty, val)
        return super()._cast_if_needed(val, target_ty)
