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
class LLVMFunctionType(LLVMType):
    arg_types: list[LLVMType]
    return_type: LLVMType

    def __str__(self):
        args = ", ".join(map(str, self.arg_types))
        return f"({args}) -> {self.return_type}"


@dataclass(frozen=True)
class LLVMPointerType(LLVMType):
    base: LLVMType
    address_space: LLVMAddressSpace = LLVMAddressSpace.GENERIC

    def __str__(self):
        return f"{self.base}*"


@dataclass(frozen=True)
class LLVMArrayType(LLVMType):
    base: LLVMType
    size: int | None = None

    def __str__(self):
        return f"[{self.size if self.size is not None else ''} x {self.base}]"


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

    def __str__(self):
        return f"{self.type} {self.value}"


@dataclass
class LLVMVar(LLVMTerm):
    name: Name

    def __str__(self):
        return f"%{self.name}"


@dataclass
class LLVMIf(LLVMTerm):
    cond: LLVMTerm
    then_t: LLVMTerm
    else_t: LLVMTerm

    def __str__(self):
        return f"if {self.cond} {{\n  {self.then_t}\n}} else {{\n  {self.else_t}\n}}"


@dataclass
class LLVMLet(LLVMTerm):
    var_name: Name
    var_value: LLVMTerm
    body: LLVMTerm

    def __str__(self):
        return f"let %{self.var_name} = {self.var_value} in\n{self.body}"


@dataclass
class LLVMAbstraction(LLVMTerm):
    arg_names: list[Name]
    arg_types: list[LLVMType]
    body: LLVMTerm

    def __str__(self):
        args_formatted = ", ".join(f"%{n}: {t}" for n, t in zip(self.arg_names, self.arg_types))
        return f"lambda({args_formatted}) -> {self.type} {{\n  {self.body}\n}}"


@dataclass
class LLVMCall(LLVMTerm):
    target: LLVMTerm
    args: list[LLVMTerm]

    def __str__(self):
        args_formatted = ", ".join(str(arg) for arg in self.args)
        return f"call {self.target}({args_formatted})"
