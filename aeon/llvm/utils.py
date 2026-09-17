from __future__ import annotations

from aeon.core.types import TypeConstructor, RefinedType, AbstractionType, Type
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
    LLVMCharType,
)

SUPPORTED_TYPES = {"Int", "Float", "Bool", "Char", "Double", "Long", "Unit", "Array", "Vector", "Buffer", "String"}
BINARY_OPS = {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||"}
UNARY_OPS = {"!", "-"}

# Opaque heap pointer for registered inductive types (Individual, List, Pair, …).
LLVMADTPtr = _ADT_PTR


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
                case "Array" | "Vector":
                    # ``Array`` is the stdlib host buffer; ``Vector`` remains as a
                    # temporary alias for older LLVM tests / local quicksort buffers.
                    return LLVMPointerType(to_llvm_type(args[0])) if args else LLVMVectorInt
                case "Buffer":
                    # Untyped Int buffer pointer used by LLVM kernels (see Buffer.ae).
                    return LLVMVectorInt
                case _ if is_registered_inductive(n.name):
                    return LLVMADTPtr
                case _:
                    return LLVMInt
        case _:
            return LLVMInt
