from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum
from typing import Any
from aeon.utils.name import Name


class LLVMType:
    pass


@dataclass(frozen=True)
class LLVMIntType(LLVMType):
    bits: int


@dataclass(frozen=True)
class LLVMFloatType(LLVMType):
    pass


@dataclass(frozen=True)
class LLVMDoubleType(LLVMType):
    pass


@dataclass(frozen=True)
class LLVMBoolType(LLVMType):
    pass


@dataclass(frozen=True)
class LLVMCharType(LLVMType):
    pass


@dataclass(frozen=True)
class LLVMVoidType(LLVMType):
    pass


class LLVMAddressSpace(IntEnum):
    GENERIC = 0
    GLOBAL = 1
    SHARED = 3
    CONSTANT = 4
    LOCAL = 5


@dataclass(frozen=True)
class LLVMPointerType(LLVMType):
    base: LLVMType
    address_space: LLVMAddressSpace = LLVMAddressSpace.GENERIC


@dataclass(frozen=True)
class LLVMArrayType(LLVMType):
    base: LLVMType
    size: int | None = None


LLVMInt = LLVMIntType(32)
LLVMLong = LLVMIntType(64)
LLVMFloat = LLVMFloatType()
LLVMDouble = LLVMDoubleType()
LLVMBool = LLVMBoolType()
LLVMChar = LLVMCharType()
LLVMVoid = LLVMVoidType()


@dataclass
class LLVMTerm:
    type: LLVMType


@dataclass
class LLVMLiteral(LLVMTerm):
    value: Any


@dataclass
class LLVMVar(LLVMTerm):
    name: Name


@dataclass
class LLVMBinOp(LLVMTerm):
    op: str
    left: LLVMTerm
    right: LLVMTerm


@dataclass
class LLVMUnaryOp(LLVMTerm):
    op: str
    arg: LLVMTerm


@dataclass
class LLVMIf(LLVMTerm):
    cond: LLVMTerm
    then_t: LLVMTerm
    else_t: LLVMTerm


@dataclass
class LLVMLet(LLVMTerm):
    var_name: Name
    var_value: LLVMTerm
    body: LLVMTerm


@dataclass
class LLVMPartialBinOp(LLVMTerm):
    op: str
    left: LLVMTerm


@dataclass
class LLVMAbstraction(LLVMTerm):
    arg_name: Name
    body: LLVMTerm


@dataclass
class LLVMApplication(LLVMTerm):
    target: LLVMTerm
    arg: LLVMTerm
