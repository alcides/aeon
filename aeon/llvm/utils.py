from __future__ import annotations

from typing import TypeGuard

from aeon.core.types import TypeConstructor, RefinedType, AbstractionType, Type, TypeVar
from aeon.utils.name import Name
from aeon.llvm.adt import is_registered_inductive, LLVMADTPtr as _ADT_PTR
from aeon.llvm.core import LLVMValidationError
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMInt,
    LLVMFloat,
    LLVMBool,
    LLVMChar,
    LLVMDouble,
    LLVMVoid,
    LLVMLong,
    LLVMFunctionType,
    LLVMVectorInt,
    LLVMPointerType,
    LLVMIntType,
    LLVMFloatType,
    LLVMDoubleType,
    LLVMBoolType,
    LLVMNDArrayType,
)

SUPPORTED_TYPES = {
    "Int",
    "Float",
    "Bool",
    "Char",
    "Double",
    "Long",
    "Unit",
    "Array",
    "Vector",
    "ReadOnly",
    "Buffer",
    "String",
    "NDArray",
    "Rank1",
    "Rank2",
    "Rank3",
}
BINARY_OPS = {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||"}
UNARY_OPS = {"!", "-"}

# Opaque heap pointer for registered inductive types (Individual, List, Pair, …).
LLVMADTPtr = _ADT_PTR


def is_array_pointer(ty: LLVMType) -> TypeGuard[LLVMPointerType]:
    """Recognize scalar array buffers, excluding opaque ADT and string pointers."""
    return isinstance(ty, LLVMPointerType) and isinstance(
        ty.element_type, (LLVMIntType, LLVMFloatType, LLVMDoubleType, LLVMBoolType)
    )


def validate_ops(op: str):
    if op not in BINARY_OPS and op not in UNARY_OPS:
        raise LLVMValidationError(f"LLVM Backend does not support operation {op}")


def sanitize_name(name: Name) -> str:
    res = name.name if name.id in (-1, 0) else f"{name.name}_{name.id}"
    return res.translate(str.maketrans(".- ", "___"))


def validate_type(ty: Type):
    match ty:
        case RefinedType(_, it, _):
            validate_type(it)
        case AbstractionType(_, vt, rt):
            validate_type(vt)
            validate_type(rt)
        case TypeConstructor(n, _) if n.name not in SUPPORTED_TYPES and not is_registered_inductive(n.name):
            raise LLVMValidationError(f"LLVM Backend does not support type {n.name}")
        case _:
            pass


def get_builtin_op_type(op: str, is_f: bool = False) -> LLVMFunctionType:
    t = LLVMFloat if is_f else LLVMInt
    if op in {"==", "!=", "<", "<=", ">", ">="}:
        return LLVMFunctionType([t, t], LLVMBool)
    if op in {"&&", "||"}:
        return LLVMFunctionType([LLVMBool, LLVMBool], LLVMBool)
    if op == "!":
        return LLVMFunctionType([LLVMBool], LLVMBool)
    if op in BINARY_OPS:
        return LLVMFunctionType([t, t], t)
    if op in UNARY_OPS:
        return LLVMFunctionType([t], t)
    raise LLVMValidationError(f"Unknown operator {op}")


def to_llvm_type(ty: Type) -> LLVMType:
    match ty:
        case RefinedType(_, it, _):
            return to_llvm_type(it)
        case AbstractionType(_, vt, rt):
            args, curr = [to_llvm_type(vt)], rt
            while isinstance(curr, AbstractionType):
                args.append(to_llvm_type(curr.var_type))
                curr = curr.type
            return LLVMFunctionType(args, to_llvm_type(curr), source_type=ty)
        case TypeConstructor(n, args):
            match n.name:
                case "Int":
                    return LLVMInt
                case "Float":
                    return LLVMFloat
                case "Double":
                    return LLVMDouble
                case "Long":
                    return LLVMLong
                case "Bool":
                    return LLVMBool
                case "Char":
                    return LLVMChar
                case "Unit":
                    return LLVMVoid
                case "Array" | "Vector" | "ReadOnly":
                    # ``Array`` is the stdlib host buffer; ``Vector`` remains as a
                    # temporary alias for older LLVM tests / local quicksort buffers.
                    return LLVMPointerType(to_llvm_type(args[0])) if args else LLVMVectorInt
                case "NDArray":
                    array_args: list[Type] = ty.args
                    if len(array_args) != 2 or not isinstance(array_args[1], (TypeConstructor, TypeVar)):
                        raise LLVMValidationError("Compiled NDArray values require a concrete rank marker")
                    ranks = {"Rank1": 1, "Rank2": 2, "Rank3": 3}
                    rank = ranks.get(array_args[1].name.name)
                    element_arg = array_args[0]
                    while isinstance(element_arg, RefinedType):
                        element_arg = element_arg.type
                    if not isinstance(element_arg, TypeConstructor) or element_arg.name.name not in {
                        "Int",
                        "Float",
                        "Bool",
                        "Long",
                        "Double",
                    }:
                        raise LLVMValidationError("Compiled NDArray values require a concrete scalar element type")
                    element = to_llvm_type(element_arg)
                    if rank is None or not isinstance(
                        element, (LLVMIntType, LLVMFloatType, LLVMDoubleType, LLVMBoolType)
                    ):
                        raise LLVMValidationError("Compiled NDArray values require rank 1, 2, or 3 and scalar elements")
                    return LLVMNDArrayType(element, rank)
                case "Buffer":
                    # Untyped Int buffer pointer used by LLVM kernels (see Buffer.ae).
                    return LLVMVectorInt
                case _ if is_registered_inductive(n.name):
                    return LLVMADTPtr
                case _:
                    return LLVMInt
        case _:
            return LLVMInt
