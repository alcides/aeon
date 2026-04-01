from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum
from typing import Any
from aeon.utils.name import Name


@dataclass(frozen=True)
class LLVMType:
    def is_pointer(self) -> bool:
        return isinstance(self, LLVMPointerType)

    def is_function(self) -> bool:
        return isinstance(self, LLVMFunctionType)


@dataclass(frozen=True)
class LLVMIntType(LLVMType):
    bits: int = 32

    def __str__(self):
        return f"i{self.bits}"


@dataclass(frozen=True)
class LLVMFloatType(LLVMType):
    def __str__(self):
        return "float"


@dataclass(frozen=True)
class LLVMDoubleType(LLVMType):
    def __str__(self):
        return "double"


@dataclass(frozen=True)
class LLVMBoolType(LLVMType):
    def __str__(self):
        return "i1"


@dataclass(frozen=True)
class LLVMCharType(LLVMType):
    def __str__(self):
        return "i8"


@dataclass(frozen=True)
class LLVMVoidType(LLVMType):
    def __str__(self):
        return "void"


class LLVMAddressSpace(IntEnum):
    GENERIC = 0
    GLOBAL = 1
    SHARED = 3
    CONSTANT = 4
    LOCAL = 5


@dataclass(frozen=True)
class LLVMPointerType(LLVMType):
    element_type: LLVMType
    address_space: LLVMAddressSpace = LLVMAddressSpace.GENERIC

    def __str__(self):
        return f"{self.element_type}*"


@dataclass(frozen=True)
class LLVMArrayType(LLVMType):
    element_type: LLVMType
    size: int | None = None

    def __str__(self):
        return f"[{self.size if self.size is not None else 0} x {self.element_type}]"


@dataclass(frozen=True)
class LLVMFunctionType(LLVMType):
    arg_types: list[LLVMType]
    return_type: LLVMType

    def __str__(self):
        args = ", ".join(str(t) for t in self.arg_types)
        return f"{self.return_type} ({args})"


LLVMInt = LLVMIntType(32)
LLVMLong = LLVMIntType(64)
LLVMFloat = LLVMFloatType()
LLVMDouble = LLVMDoubleType()
LLVMBool = LLVMBoolType()
LLVMChar = LLVMCharType()
LLVMVoid = LLVMVoidType()
LLVMVectorInt = LLVMPointerType(LLVMInt)
LLVMVectorFloat = LLVMPointerType(LLVMFloat)
LLVMVectorDouble = LLVMPointerType(LLVMDouble)

VECTOR_OPERATIONS: frozenset[str] = frozenset(
    [
        "Vector_map",
        "Vector_reduce",
        "Vector_imap",
        "Vector_filter",
        "Vector_zipWith",
        "Vector_count",
    ]
)


@dataclass
class LLVMTerm:
    type: LLVMType


@dataclass
class LLVMLiteral(LLVMTerm):
    value: Any

    def __str__(self):
        return str(self.value)


@dataclass
class LLVMVar(LLVMTerm):
    name: Name

    def __str__(self):
        return self.name.name


@dataclass
class LLVMIf(LLVMTerm):
    cond: LLVMTerm
    then_t: LLVMTerm
    else_t: LLVMTerm

    def __str__(self):
        return f"if {self.cond} then {self.then_t} else {self.else_t}"


@dataclass
class LLVMLet(LLVMTerm):
    var_name: Name
    var_value: LLVMTerm
    body: LLVMTerm

    def __str__(self):
        return f"let {self.var_name.name} = {self.var_value} in {self.body}"


@dataclass
class LLVMFunction(LLVMTerm):
    arg_names: list[Name]
    arg_types: list[LLVMType]
    body: LLVMTerm
    name: Name | None = None

    def __str__(self):
        args = ", ".join(f"{n.name}:{t}" for n, t in zip(self.arg_names, self.arg_types))
        return f"\\{args} -> {self.body}"


@dataclass
class LLVMCall(LLVMTerm):
    target: LLVMTerm
    args: list[LLVMTerm]

    def __str__(self):
        args = ", ".join(str(a) for a in self.args)
        return f"{self.target}({args})"


@dataclass
class LLVMGetElementPtr(LLVMTerm):
    ptr: LLVMTerm
    indices: list[LLVMTerm]

    def __str__(self):
        indices = ", ".join(str(i) for i in self.indices)
        return f"gep {self.ptr}, {indices}"


@dataclass
class LLVMLoad(LLVMTerm):
    ptr: LLVMTerm

    def __str__(self):
        return f"load {self.ptr}"


@dataclass
class LLVMStore(LLVMTerm):
    value: LLVMTerm
    ptr: LLVMTerm

    def __str__(self):
        return f"store {self.value}, {self.ptr}"


@dataclass
class LLVMAlloc(LLVMTerm):
    def __str__(self):
        return f"alloca {self.type}"


@dataclass
class LLVMVectorOp(LLVMTerm):
    f: LLVMTerm
    v: LLVMTerm
    size: LLVMTerm


@dataclass
class LLVMVectorMap(LLVMVectorOp):
    def __str__(self):
        return f"vector_map {self.f}, {self.v}, {self.size}"


@dataclass
class LLVMVectorReduce(LLVMTerm):
    f: LLVMTerm
    initial: LLVMTerm
    v: LLVMTerm
    size: LLVMTerm

    def __str__(self):
        return f"vector_reduce {self.f}, {self.initial}, {self.v}, {self.size}"


@dataclass
class LLVMVectorIMap(LLVMVectorOp):
    def __str__(self):
        return f"vector_imap {self.f}, {self.v}, {self.size}"


@dataclass
class LLVMVectorFilter(LLVMVectorOp):
    def __str__(self):
        return f"vector_filter {self.f}, {self.v}, {self.size}"


@dataclass
class LLVMVectorZipWith(LLVMTerm):
    f: LLVMTerm
    v1: LLVMTerm
    v2: LLVMTerm
    size: LLVMTerm

    def __str__(self):
        return f"vector_zipWith {self.f}, {self.v1}, {self.v2}, {self.size}"


@dataclass
class LLVMVectorCount(LLVMVectorOp):
    def __str__(self):
        return f"vector_count {self.f}, {self.v}, {self.size}"


@dataclass
class LLVMVectorSet(LLVMTerm):
    ptr: LLVMTerm
    index: LLVMTerm
    value: LLVMTerm

    def __str__(self):
        return f"vector_set {self.ptr}, {self.index}, {self.value}"
