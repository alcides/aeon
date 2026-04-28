from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum
from typing import Any
import llvmlite.ir as ir
from aeon.utils.name import Name
from aeon.llvm.core import LLVMVisitor


@dataclass
class LLVMType:
    def to_ir(self) -> ir.Type:
        raise NotImplementedError


@dataclass
class LLVMIntType(LLVMType):
    bits: int = 32

    def __str__(self):
        return f"i{self.bits}"

    def to_ir(self) -> ir.Type:
        return ir.IntType(self.bits)


@dataclass
class LLVMFloatType(LLVMType):
    def __str__(self):
        return "float"

    def to_ir(self) -> ir.Type:
        return ir.FloatType()


@dataclass
class LLVMDoubleType(LLVMType):
    def __str__(self):
        return "double"

    def to_ir(self) -> ir.Type:
        return ir.DoubleType()


@dataclass
class LLVMBoolType(LLVMType):
    def __str__(self):
        return "i1"

    def to_ir(self) -> ir.Type:
        return ir.IntType(1)


@dataclass
class LLVMVoidType(LLVMType):
    def __str__(self):
        return "void"

    def to_ir(self) -> ir.Type:
        return ir.VoidType()


@dataclass
class LLVMCharType(LLVMType):
    def __str__(self):
        return "i8"

    def to_ir(self) -> ir.Type:
        return ir.IntType(8)


class LLVMAddressSpace(IntEnum):
    GENERIC = 0
    GLOBAL = 1
    SHARED = 3
    LOCAL = 5


@dataclass
class LLVMPointerType(LLVMType):
    element_type: LLVMType
    address_space: LLVMAddressSpace = LLVMAddressSpace.GENERIC

    def __str__(self):
        return f"{self.element_type}*"

    def to_ir(self) -> ir.Type:
        base = self.element_type.to_ir()
        if isinstance(base, ir.VoidType):
            base = ir.IntType(8)
        return ir.PointerType(base, addrspace=int(self.address_space))


@dataclass
class LLVMFunctionType(LLVMType):
    arg_types: list[LLVMType]
    return_type: LLVMType

    def __str__(self):
        args = ", ".join(str(t) for t in self.arg_types)
        return f"{self.return_type} ({args})"

    def to_ir(self) -> ir.Type:
        return ir.FunctionType(self.return_type.to_ir(), [t.to_ir() for t in self.arg_types])


LLVMInt = LLVMIntType()
LLVMLong = LLVMIntType(64)
LLVMFloat = LLVMFloatType()
LLVMDouble = LLVMDoubleType()
LLVMBool = LLVMBoolType()
LLVMVoid = LLVMVoidType()
LLVMChar = LLVMCharType()

LLVMVectorInt = LLVMPointerType(LLVMInt)
LLVMVectorLong = LLVMPointerType(LLVMLong)
LLVMVectorFloat = LLVMPointerType(LLVMFloat)
LLVMVectorDouble = LLVMPointerType(LLVMDouble)
LLVMVectorBool = LLVMPointerType(LLVMBool)
LLVMVectorChar = LLVMPointerType(LLVMChar)

VECTOR_OPERATIONS = {
    "Vector_map",
    "Vector_reduce",
    "Vector_imap",
    "Vector_filter",
    "Vector_zipWith",
    "Vector_count",
    "Vector_size",
}


@dataclass
class LLVMTerm:
    type: LLVMType

    def accept(self, visitor: LLVMVisitor) -> Any:
        raise NotImplementedError

    def find_calls(self) -> set[Name]:
        return set()


@dataclass
class LLVMLiteral(LLVMTerm):
    value: Any

    def __str__(self):
        return f"{self.type} {self.value}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_literal(self)


@dataclass
class LLVMVar(LLVMTerm):
    name: Name

    def __str__(self):
        return str(self.name)

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_var(self)

    def find_calls(self) -> set[Name]:
        return {self.name}


@dataclass
class LLVMIf(LLVMTerm):
    cond: LLVMTerm
    then_t: LLVMTerm
    else_t: LLVMTerm

    def __str__(self):
        return f"if {self.cond} then {self.then_t} else {self.else_t}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_if(self)

    def find_calls(self) -> set[Name]:
        return self.cond.find_calls() | self.then_t.find_calls() | self.else_t.find_calls()


@dataclass
class LLVMLet(LLVMTerm):
    var_name: Name
    var_value: LLVMTerm
    body: LLVMTerm

    def __str__(self):
        return f"let {self.var_name} = {self.var_value} in {self.body}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_let(self)

    def find_calls(self) -> set[Name]:
        return self.var_value.find_calls() | self.body.find_calls()


@dataclass
class LLVMFunction(LLVMTerm):
    arg_names: list[Name]
    arg_types: list[LLVMType]
    body: LLVMTerm
    name: Name | None = None

    def __str__(self):
        name_str = f" @{self.name}" if self.name else ""
        return f"fn{name_str} {self.type} {self.arg_names} {self.body}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_function(self)

    def find_calls(self) -> set[Name]:
        names = self.body.find_calls()
        if self.name:
            names.add(self.name)
        return names


@dataclass
class LLVMCall(LLVMTerm):
    target: LLVMTerm
    args: list[LLVMTerm]

    def __post_init__(self):
        # Flatten if needed
        new_args = []
        for a in self.args:
            if isinstance(a, list):
                new_args.extend(a)
            else:
                new_args.append(a)
        self.args = new_args

    def __str__(self):
        args = ", ".join(str(a) for a in self.args)
        return f"call {self.target}({args})"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_call(self)

    def find_calls(self) -> set[Name]:
        names = self.target.find_calls()
        for a in self.args:
            names |= a.find_calls()
        return names


@dataclass
class LLVMCast(LLVMTerm):
    val: LLVMTerm

    def __str__(self):
        return f"cast {self.val} to {self.type}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_cast(self)

    def find_calls(self) -> set[Name]:
        return self.val.find_calls()


@dataclass
class LLVMGetElementPtr(LLVMTerm):
    ptr: LLVMTerm
    indices: list[LLVMTerm]

    def __str__(self):
        indices = ", ".join(str(i) for i in self.indices)
        return f"gep {self.ptr}, {indices}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_gep(self)

    def find_calls(self) -> set[Name]:
        names = self.ptr.find_calls()
        for i in self.indices:
            names |= i.find_calls()
        return names


@dataclass
class LLVMLoad(LLVMTerm):
    ptr: LLVMTerm

    def __str__(self):
        return f"load {self.ptr}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_load(self)

    def find_calls(self) -> set[Name]:
        return self.ptr.find_calls()


@dataclass
class LLVMStore(LLVMTerm):
    value: LLVMTerm
    ptr: LLVMTerm

    def __str__(self):
        return f"store {self.value}, {self.ptr}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_store(self)

    def find_calls(self) -> set[Name]:
        return self.value.find_calls() | self.ptr.find_calls()


@dataclass
class LLVMAlloc(LLVMTerm):
    def __str__(self):
        return f"alloca {self.type}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_alloc(self)


@dataclass
class LLVMVectorOp(LLVMTerm):
    f: LLVMTerm
    v: LLVMTerm
    size: LLVMTerm

    def find_calls(self) -> set[Name]:
        return self.f.find_calls() | self.v.find_calls() | self.size.find_calls()


@dataclass
class LLVMVectorMap(LLVMVectorOp):
    def __str__(self):
        return f"vector_map {self.f}, {self.v}, {self.size}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_map(self)


@dataclass
class LLVMVectorReduce(LLVMTerm):
    f: LLVMTerm
    initial: LLVMTerm
    v: LLVMTerm
    size: LLVMTerm

    def __str__(self):
        return f"vector_reduce {self.f}, {self.initial}, {self.v}, {self.size}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_reduce(self)

    def find_calls(self) -> set[Name]:
        return self.f.find_calls() | self.initial.find_calls() | self.v.find_calls() | self.size.find_calls()


@dataclass
class LLVMVectorIMap(LLVMVectorOp):
    def __str__(self):
        return f"vector_imap {self.f}, {self.v}, {self.size}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_imap(self)


@dataclass
class LLVMVectorFilter(LLVMVectorOp):
    def __str__(self):
        return f"vector_filter {self.f}, {self.v}, {self.size}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_filter(self)


@dataclass
class LLVMVectorZipWith(LLVMTerm):
    f: LLVMTerm
    v1: LLVMTerm
    v2: LLVMTerm
    size: LLVMTerm

    def __str__(self):
        return f"vector_zipWith {self.f}, {self.v1}, {self.v2}, {self.size}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_zipwith(self)

    def find_calls(self) -> set[Name]:
        return self.f.find_calls() | self.v1.find_calls() | self.v2.find_calls() | self.size.find_calls()


@dataclass
class LLVMVectorCount(LLVMVectorOp):
    def __str__(self):
        return f"vector_count {self.f}, {self.v}, {self.size}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_count(self)


@dataclass
class LLVMVectorGet(LLVMTerm):
    v: LLVMTerm
    index: LLVMTerm

    def __str__(self):
        return f"vector_get {self.v}[{self.index}]"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_get(self)

    def find_calls(self) -> set[Name]:
        return self.v.find_calls() | self.index.find_calls()


@dataclass
class LLVMVectorSet(LLVMTerm):
    v: LLVMTerm
    index: LLVMTerm
    value: LLVMTerm

    def __str__(self):
        return f"vector_set {self.v}[{self.index}] = {self.value}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_set(self)

    def find_calls(self) -> set[Name]:
        return self.v.find_calls() | self.index.find_calls() | self.value.find_calls()


@dataclass
class LLVMVectorSize(LLVMTerm):
    v: LLVMTerm

    def __str__(self):
        return f"vector_size {self.v}"

    def accept(self, visitor: LLVMVisitor) -> Any:
        return visitor.visit_vector_size(self)

    def find_calls(self) -> set[Name]:
        return self.v.find_calls()
