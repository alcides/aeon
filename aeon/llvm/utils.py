from __future__ import annotations

from aeon.core.types import TypeConstructor, RefinedType, AbstractionType, Type
from aeon.utils.name import Name
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
)

SUPPORTED_TYPES = {"Int", "Float", "Bool", "Char", "Double", "Long", "Unit"}
BINARY_OPS = {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||"}
UNARY_OPS = {"!", "-"}


def validate_ops(op: str):
    if op.startswith("anf"):
        return
    if op not in BINARY_OPS and op not in UNARY_OPS:
        raise LLVMValidationError(f"LLVM Backend does not support operation {op}")


def sanitize_name(name: Name | str) -> str:
    if isinstance(name, Name):
        name_str = name.name
        if name.id != -1 and name.id != 0:
            name_str = f"{name_str}_{name.id}"
    else:
        name_str = str(name)
    return name_str.replace(".", "_").replace("-", "_").replace(" ", "_")


def validate_type(ty: Type):
    match ty:
        case RefinedType(_, inner_type, _):
            validate_type(inner_type)
        case AbstractionType(_, var_type, return_type):
            validate_type(var_type)
            validate_type(return_type)
        case TypeConstructor(name, _):
            if name.name not in SUPPORTED_TYPES:
                raise LLVMValidationError(f"LLVM Backend does not support type {name.name}")
        case _:
            pass


def get_builtin_op_type(op: str, is_float: bool = False) -> LLVMFunctionType:
    if op in BINARY_OPS:
        if op in {"==", "!=", "<", "<=", ">", ">="}:
            return LLVMFunctionType(
                arg_types=[LLVMFloat if is_float else LLVMInt, LLVMFloat if is_float else LLVMInt], return_type=LLVMBool
            )
        elif op in {"&&", "||"}:
            return LLVMFunctionType(arg_types=[LLVMBool, LLVMBool], return_type=LLVMBool)
        else:
            return LLVMFunctionType(
                arg_types=[LLVMFloat if is_float else LLVMInt, LLVMFloat if is_float else LLVMInt],
                return_type=LLVMFloat if is_float else LLVMInt,
            )
    elif op in UNARY_OPS:
        if op == "!":
            return LLVMFunctionType(arg_types=[LLVMBool], return_type=LLVMBool)
        else:
            return LLVMFunctionType(
                arg_types=[LLVMFloat if is_float else LLVMInt], return_type=LLVMFloat if is_float else LLVMInt
            )
    raise LLVMValidationError(f"Unknown operator {op}")


def from_type_to_llvm_type(ty: Type) -> LLVMType:
    match ty:
        case RefinedType(_, inner_type, _):
            return from_type_to_llvm_type(inner_type)
        case AbstractionType(_, var_type, return_type):
            arg_types = [from_type_to_llvm_type(var_type)]
            curr = return_type
            while isinstance(curr, AbstractionType):
                arg_types.append(from_type_to_llvm_type(curr.var_type))
                curr = curr.type
            return LLVMFunctionType(arg_types=arg_types, return_type=from_type_to_llvm_type(curr))
        case TypeConstructor(name, args):
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
                case "Vector":
                    if args:
                        element_type = from_type_to_llvm_type(args[0])
                        return LLVMPointerType(element_type)
                    return LLVMVectorInt
                case _:
                    return LLVMInt
        case _:
            return LLVMInt
