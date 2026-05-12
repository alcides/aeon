from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum
from typing import Any

import numpy as np

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


class VectorDType(IntEnum):
    INT = 0
    FLOAT32 = 1
    INT64 = 2
    FLOAT64 = 3
    OBJECT = 4

    @property
    def np_dtype(self) -> type[np.generic] | None:
        return _VECTOR_NP_DTYPES.get(self)

    @classmethod
    def from_value(cls, value: object) -> VectorDType | None:
        if isinstance(value, bool):
            return cls.INT
        if isinstance(value, (int, np.integer)):
            v = int(value)
            if -(2**31) <= v <= 2**31 - 1:
                return cls.INT
            return cls.INT64
        if isinstance(value, np.float32):
            return cls.FLOAT32
        if isinstance(value, np.float64):
            return cls.FLOAT64
        if isinstance(value, (float, np.floating)):
            return cls.FLOAT64
        return None

    @classmethod
    def promote(cls, curr: VectorDType, incoming: VectorDType) -> VectorDType:
        if curr == incoming:
            return curr
        if curr == cls.OBJECT or incoming == cls.OBJECT:
            return cls.OBJECT
        return curr if curr >= incoming else incoming


_VECTOR_NP_DTYPES: dict[VectorDType, type[np.generic]] = {
    VectorDType.INT: np.int32,
    VectorDType.FLOAT32: np.float32,
    VectorDType.INT64: np.int64,
    VectorDType.FLOAT64: np.float64,
}


def _resolve_type_constructor_name(name: Name) -> tuple[str, str]:
    qualified_name = name.name
    unqualified_name = qualified_name.rsplit(".", 1)[-1]
    return qualified_name, unqualified_name


def _is_supported_builtin_type(name: Name) -> bool:
    _, unqualified_name = _resolve_type_constructor_name(name)
    return unqualified_name in SUPPORTED_TYPES and name.id == 0


def validate_ops(op: str) -> None:
    if not op.startswith("anf") and op not in BINARY_OPS and op not in UNARY_OPS:
        raise LLVMValidationError(f"unsupported LLVM op: {op}")


@dataclass
class RawVector:
    size: int
    dtype: VectorDType = VectorDType.INT
    arr: np.ndarray | None = None
    obj: list[Any] | None = None
    freed: bool = False

    @classmethod
    def from_list(cls, values: list[Any]) -> RawVector:
        if not values:
            return cls(0, VectorDType.INT)

        inferred = VectorDType.INT
        for value in values:
            incoming = VectorDType.from_value(value)
            if incoming is None:
                out = cls(0, VectorDType.OBJECT)
                out.obj = list(values)
                out.size = len(out.obj)
                return out
            inferred = VectorDType.promote(inferred, incoming)

        out = cls(len(values), inferred)
        if inferred == VectorDType.OBJECT:
            out.obj = list(values)
            out.arr = None
            return out

        np_dtype = inferred.np_dtype
        if np_dtype is None:
            raise LLVMValidationError(f"unsupported dtype: {inferred}")
        out.arr = np.asarray(values, dtype=np_dtype)
        out.obj = None
        return out

    @classmethod
    def from_numpy(cls, arr: np.ndarray) -> RawVector:
        if arr.ndim != 1:
            raise ValueError("expected 1D array")
        dtype_map = {
            np.dtype(np.int32): VectorDType.INT,
            np.dtype(np.int64): VectorDType.INT64,
            np.dtype(np.float32): VectorDType.FLOAT32,
            np.dtype(np.float64): VectorDType.FLOAT64,
        }
        vec_dtype = dtype_map.get(arr.dtype, VectorDType.OBJECT)
        if vec_dtype == VectorDType.OBJECT:
            out = cls(0, VectorDType.OBJECT)
            out.obj = arr.tolist()
            out.size = len(out.obj)
            return out
        out = cls(int(arr.shape[0]), vec_dtype)
        out.arr = arr
        out.obj = None
        return out

    def __post_init__(self) -> None:
        if self.size < 0:
            raise ValueError("vector size must be >= 0")
        if self.dtype == VectorDType.OBJECT:
            self.obj = [None] * self.size
            return
        np_dtype = self.dtype.np_dtype
        if np_dtype is None:
            raise LLVMValidationError(f"unsupported dtype: {self.dtype}")
        self.arr = np.zeros(self.size, dtype=np_dtype)

    def _ensure_not_freed(self) -> None:
        if self.freed:
            raise RuntimeError("vector already freed")

    def _promote_to_object(self) -> None:
        if self.dtype == VectorDType.OBJECT:
            return
        if self.arr is None:
            raise RuntimeError("vector has no numeric storage")
        self.obj = self.arr.tolist()
        self.arr = None
        self.dtype = VectorDType.OBJECT

    def _promote_to(self, target: VectorDType) -> None:
        if self.dtype == target:
            return
        if self.dtype == VectorDType.OBJECT or target == VectorDType.OBJECT:
            self._promote_to_object()
            return
        if self.arr is None:
            raise RuntimeError("vector has no numeric storage")
        if target.np_dtype is None:
            raise LLVMValidationError(f"unsupported dtype: {target}")
        self.arr = self.arr.astype(target.np_dtype, copy=False)
        self.dtype = target

    def _prepare_for_value(self, value: Any) -> None:
        incoming = VectorDType.from_value(value)
        if self.dtype == VectorDType.OBJECT or incoming is None:
            if self.dtype != VectorDType.OBJECT:
                self._promote_to_object()
            return
        target = VectorDType.promote(self.dtype, incoming)
        self._promote_to(target)

    def get(self, index: int) -> Any:
        self._ensure_not_freed()
        if index < 0 or index >= self.size:
            raise IndexError("index out of range")
        if self.dtype == VectorDType.OBJECT:
            if self.obj is None:
                raise RuntimeError("vector has no object storage")
            return self.obj[index]
        if self.arr is None:
            raise RuntimeError("vector has no numeric storage")
        item = self.arr[index]
        return item.item() if hasattr(item, "item") else item

    def set(self, index: int, value: Any) -> RawVector:
        self._ensure_not_freed()
        if index < 0 or index >= self.size:
            raise IndexError("index out of range")
        self._prepare_for_value(value)
        if self.dtype == VectorDType.OBJECT:
            if self.obj is None:
                raise RuntimeError("vector has no object storage")
            self.obj[index] = value
            return self
        if self.arr is None:
            raise RuntimeError("vector has no numeric storage")
        self.arr[index] = value
        return self

    def append(self, value: Any) -> RawVector:
        self._ensure_not_freed()
        self._prepare_for_value(value)
        if self.dtype == VectorDType.OBJECT:
            if self.obj is None:
                raise RuntimeError("vector has no object storage")
            self.obj.append(value)
            self.size += 1
            return self
        if self.arr is None:
            raise RuntimeError("vector has no numeric storage")
        self.arr = np.append(self.arr, value)
        self.size = int(self.arr.shape[0])
        return self

    def to_list(self) -> list[Any]:
        self._ensure_not_freed()
        if self.dtype == VectorDType.OBJECT:
            if self.obj is None:
                raise RuntimeError("vector has no object storage")
            return list(self.obj)
        if self.arr is None:
            raise RuntimeError("vector has no numeric storage")
        return self.arr.tolist()

    def __iter__(self):
        self._ensure_not_freed()
        if self.dtype == VectorDType.OBJECT:
            return iter(self.obj) if self.obj is not None else iter([])
        if self.arr is not None:
            return (x.item() if hasattr(x, "item") else x for x in self.arr)
        return iter([])

    def __len__(self) -> int:
        return self.size

    def __getitem__(self, index: int) -> Any:
        return self.get(index)

    def free(self) -> int:
        if self.freed:
            return 0
        self.arr = None
        self.obj = None
        self.size = 0
        self.freed = True
        return 0


def ensure_raw_vector(v: Any) -> RawVector:
    if isinstance(v, RawVector):
        return v
    if isinstance(v, np.ndarray):
        return RawVector.from_numpy(v)
    if isinstance(v, list):
        return RawVector.from_list(v)
    raise TypeError("expected a Vector value")


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
