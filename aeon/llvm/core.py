from __future__ import annotations

from dataclasses import dataclass
from abc import ABC, abstractmethod
from typing import Dict, Any, List, TYPE_CHECKING
from aeon.core.terms import Term
from aeon.utils.name import Name

if TYPE_CHECKING:
    from aeon.llvm.llvm_ast import (
        LLVMTerm,
        LLVMType,
        LLVMLiteral,
        LLVMVar,
        LLVMIf,
        LLVMLet,
        LLVMFunction,
        LLVMCall,
        LLVMCast,
        LLVMGetElementPtr,
        LLVMLoad,
        LLVMStore,
        LLVMAlloc,
        LLVMVectorMap,
        LLVMVectorReduce,
        LLVMVectorIMap,
        LLVMVectorFilter,
        LLVMVectorZipWith,
        LLVMVectorCount,
        LLVMVectorGet,
        LLVMVectorSet,
        LLVMVectorSize,
    )
else:
    LLVMTerm = Any
    LLVMType = Any
    LLVMLiteral = Any
    LLVMVar = Any
    LLVMIf = Any
    LLVMLet = Any
    LLVMFunction = Any
    LLVMCall = Any
    LLVMCast = Any
    LLVMGetElementPtr = Any
    LLVMLoad = Any
    LLVMStore = Any
    LLVMAlloc = Any
    LLVMVectorMap = Any
    LLVMVectorReduce = Any
    LLVMVectorIMap = Any
    LLVMVectorFilter = Any
    LLVMVectorZipWith = Any
    LLVMVectorCount = Any
    LLVMVectorGet = Any
    LLVMVectorSet = Any
    LLVMVectorSize = Any


class LLVMBackendError(Exception):
    pass


class LLVMValidationError(LLVMBackendError):
    pass


@dataclass(frozen=True)
class ValidationContext:
    pass


class ValidationStep(ABC):
    @abstractmethod
    def validate(self, t: Term, ctx: ValidationContext) -> None:
        pass


class LLVMLowerer(ABC):
    def validate(self, t: Term, ctx: ValidationContext) -> None:
        for step in self.get_validation_steps():
            step.validate(t, ctx)

    @abstractmethod
    def get_validation_steps(self) -> List[ValidationStep]:
        pass

    @abstractmethod
    def lower(
        self,
        t: Term,
        expected_type: LLVMType = None,
        type_env: Dict[Name, LLVMType] = None,
        env: Dict[Name, LLVMTerm] = None,
    ) -> LLVMTerm:
        pass

    @abstractmethod
    def get_signature(self, ty: LLVMType) -> tuple[List[LLVMType], LLVMType]:
        pass


class LLVMIRGenerator(ABC):
    @abstractmethod
    def generate_ir(self, definitions: List[LLVMTerm]) -> str:
        pass


class LLVMOptimizer(ABC):
    @abstractmethod
    def optimize(self, llvm_ir: str, opt_level: int = 3) -> str:
        pass


class LLVMExecutionEngine(ABC):
    @abstractmethod
    def execute(
        self, llvm_ir: str, func_name: str, args: List[Any], arg_types: List[LLVMType], ret_type: LLVMType
    ) -> Any:
        pass


@dataclass
class Backend:
    executor: LLVMExecutionEngine
    generator: LLVMIRGenerator
    lowerer: LLVMLowerer


class LLVMPipeline(ABC):
    @abstractmethod
    def compile(self, program: Term) -> None:
        pass

    @abstractmethod
    def get_curried_function(self, name: Name, native_fallback: Any = None) -> Any:
        pass

    @abstractmethod
    def invoke(self, name_id: Name, arguments: List[Any]) -> Any:
        pass


class LLVMVisitor(ABC):
    @abstractmethod
    def visit(self, node: LLVMTerm) -> Any:
        pass

    @abstractmethod
    def visit_literal(self, node: LLVMLiteral) -> Any:
        pass

    @abstractmethod
    def visit_var(self, node: LLVMVar) -> Any:
        pass

    @abstractmethod
    def visit_if(self, node: LLVMIf) -> Any:
        pass

    @abstractmethod
    def visit_let(self, node: LLVMLet) -> Any:
        pass

    @abstractmethod
    def visit_function(self, node: LLVMFunction) -> Any:
        pass

    @abstractmethod
    def visit_call(self, node: LLVMCall) -> Any:
        pass

    @abstractmethod
    def visit_cast(self, node: LLVMCast) -> Any:
        pass

    @abstractmethod
    def visit_gep(self, node: LLVMGetElementPtr) -> Any:
        pass

    @abstractmethod
    def visit_load(self, node: LLVMLoad) -> Any:
        pass

    @abstractmethod
    def visit_store(self, node: LLVMStore) -> Any:
        pass

    @abstractmethod
    def visit_alloc(self, node: LLVMAlloc) -> Any:
        pass

    @abstractmethod
    def visit_vector_map(self, node: LLVMVectorMap) -> Any:
        pass

    @abstractmethod
    def visit_vector_reduce(self, node: LLVMVectorReduce) -> Any:
        pass

    @abstractmethod
    def visit_vector_imap(self, node: LLVMVectorIMap) -> Any:
        pass

    @abstractmethod
    def visit_vector_filter(self, node: LLVMVectorFilter) -> Any:
        pass

    @abstractmethod
    def visit_vector_zipwith(self, node: LLVMVectorZipWith) -> Any:
        pass

    @abstractmethod
    def visit_vector_count(self, node: LLVMVectorCount) -> Any:
        pass

    @abstractmethod
    def visit_vector_get(self, node: LLVMVectorGet) -> Any:
        pass

    @abstractmethod
    def visit_vector_set(self, node: LLVMVectorSet) -> Any:
        pass

    @abstractmethod
    def visit_vector_size(self, node: LLVMVectorSize) -> Any:
        pass
