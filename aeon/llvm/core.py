from __future__ import annotations

from dataclasses import dataclass
from abc import ABC, abstractmethod
from typing import Dict, Any, List
from aeon.core.terms import Term
from aeon.utils.name import Name
from aeon.llvm.llvm_ast import LLVMTerm, LLVMType


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


class LLVMIRGenerator(ABC):
    @abstractmethod
    def generate_kernels(self, kernels: List[LLVMTerm]) -> str:
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
