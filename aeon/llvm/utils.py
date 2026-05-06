from __future__ import annotations

from aeon.core.types import (
    TypeConstructor,
    RefinedType,
    AbstractionType,
    Type,
    TypePolymorphism,
    RefinementPolymorphism,
    TypeVar,
    Top,
)
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

SUPPORTED_TYPES = {"Int", "Float", "Bool", "Char", "Double", "Long", "Unit", "Vector", "String"}
BINARY_OPS = {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||"}
UNARY_OPS = {"!", "-"}


def _resolve_type_constructor_name(name: Name) -> tuple[str, str]:
    qualified_name = name.name
    unqualified_name = qualified_name.rsplit(".", 1)[-1]
    return qualified_name, unqualified_name


def _is_supported_builtin_type(name: Name) -> bool:
    _, unqualified_name = _resolve_type_constructor_name(name)
    return unqualified_name in SUPPORTED_TYPES and name.id == 0


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
        case TypePolymorphism(_, _, body):
            validate_type(body)
        case RefinementPolymorphism(_, _, body):
            validate_type(body)
        case TypeConstructor(n, _) if not _is_supported_builtin_type(n):
            raise LLVMValidationError(f"LLVM Backend doesn't support support type {n.name}")
        case TypeVar(name):
            _ = name
            pass
        case Top():
            raise LLVMValidationError("LLVM Backend doesn't support support Top type")
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
        case TypePolymorphism(_, _, body):
            return to_llvm_type(body)
        case RefinementPolymorphism(_, _, body):
            return to_llvm_type(body)
        case AbstractionType(_, vt, rt):
            args, curr = [to_llvm_type(vt)], rt
            while isinstance(curr, AbstractionType):
                args.append(to_llvm_type(curr.var_type))
                curr = curr.type
            return LLVMFunctionType(args, to_llvm_type(curr))
        case TypeConstructor(n, args):
            _, unqualified_name = _resolve_type_constructor_name(n)
            if not _is_supported_builtin_type(n):
                raise LLVMValidationError(f"LLVM Backend doesn't support non-builtin type {n}")

            match unqualified_name:
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
                    if not args:
                        return LLVMVectorInt
                    try:
                        return LLVMPointerType(to_llvm_type(args[0]))
                    except LLVMValidationError:
                        return LLVMPointerType(LLVMInt)
                case "String":
                    return LLVMPointerType(LLVMChar)
                case _:
                    raise LLVMValidationError(f"LLVM Backend doesn't support builtin type {n}")
        case TypeVar(name):
            _ = name
            return LLVMInt
        case _:
            raise LLVMValidationError(f"LLVM Backend doesn't support non-builtin type {ty.__repr__()}")
