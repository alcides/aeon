from __future__ import annotations

from aeon.core.types import TypeConstructor, RefinedType, AbstractionType, Type
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
)

SUPPORTED_TYPES = {"Int", "Float", "Bool", "Char", "Double", "Long", "Unit"}
BINARY_OPS = {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||"}
UNARY_OPS = {"!", "-"}


def validate_ops(op: str):
    if op.startswith("anf"):
        return
    if op not in BINARY_OPS and op not in UNARY_OPS:
        raise LLVMValidationError(f"LLVM Backend does not support operation {op}")


def validate_type(ty: Type):
    match ty:
        case RefinedType(_, inner):
            validate_type(inner)
        case AbstractionType(_, var_ty, ret_ty):
            validate_type(var_ty)
            validate_type(ret_ty)
        case TypeConstructor(name):
            if name.name not in SUPPORTED_TYPES:
                raise LLVMValidationError(f"LLVM Backend does not support type: {name.name}")
        case _:
            pass


def from_type_to_llvm_type(ty) -> LLVMType:
    match ty:
        case RefinedType(inner_type, _):
            return from_type_to_llvm_type(inner_type)
        case AbstractionType(_, _, return_type):
            return from_type_to_llvm_type(return_type)
        case TypeConstructor(name):
            match name.name:
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
                case _:
                    return LLVMInt
        case _:
            return LLVMInt
