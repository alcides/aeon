from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Dict, Any, List
from aeon.core.terms import Term
from aeon.utils.name import Name
from aeon.llvm.llvm_ast import LLVMTerm, LLVMType


class LLVMLowerer(ABC):
    @abstractmethod
    def validate(self, t: Term, rec_scope: set[Name] = None, env_names: set[str] = None) -> None:
        pass

    @abstractmethod
    def lower(self, t: Term, type_env: Dict[Name, LLVMType] = None, env: Dict[Name, LLVMTerm] = None) -> LLVMTerm:
        pass


class LLVMIRGenerator(ABC):
    @abstractmethod
    def generate(self, backend_ast: LLVMTerm) -> str:
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
