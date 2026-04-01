from __future__ import annotations

from typing import Any, Dict

from loguru import logger

from aeon.core.terms import Term, Let, Rec
from aeon.core.types import Type
from aeon.llvm.core import (
    LLVMExecutionEngine,
    LLVMIRGenerator,
    LLVMLowerer,
    LLVMBackendError,
    LLVMPipeline,
)
from aeon.llvm.llvm_ast import LLVMFunction, LLVMTerm
from aeon.llvm.utils import sanitize_name, to_llvm_type
from aeon.utils.name import Name


class CPULLVMPipeline(LLVMPipeline):
    def __init__(
        self,
        executor: LLVMExecutionEngine,
        generator: LLVMIRGenerator,
        lowerer: LLVMLowerer,
        metadata: Dict[Name, Any] | None = None,
        debug: bool = False,
    ):
        self.executor = executor
        self.generator = generator
        self.lowerer = lowerer
        self.metadata = metadata or {}
        self.debug = debug
        self.compiled_functions: Dict[Name, LLVMTerm] = {}
        self.name_to_id_cache: Dict[str, Name] = {}
        self.type_environment: Dict[Name, Type] = {}
        self.llvm_ir: str = ""

    def compile(self, program: Term):
        discovered_targets = self._find_compilation_targets(program)

        for target_id, target_body in discovered_targets.items():
            target_type = self.type_environment[target_id]
            target_llvm_type = to_llvm_type(target_type)

            llvm_ast = self.lowerer.lower(
                target_body,
                expected_type=target_llvm_type,
                type_env={fid: to_llvm_type(ty) for fid, ty in self.type_environment.items()},
                env={fid: value for fid, value in self.compiled_functions.items()},
            )

            if isinstance(llvm_ast, LLVMFunction):
                llvm_ast.name = target_id

            self.compiled_functions[target_id] = llvm_ast

        self.llvm_ir = self.generator.generate_ir(list(self.compiled_functions.values()))
        if self.debug:
            logger.debug(self.llvm_ir)

    def _find_compilation_targets(self, term: Term) -> Dict[Name, Term]:
        discovery_targets = {}
        current_term = term

        while isinstance(current_term, (Let, Rec)):
            if isinstance(current_term, Rec):
                target_id = current_term.var_name
                target_name = target_id.name

                self.type_environment[target_id] = current_term.var_type
                self.name_to_id_cache[target_name] = target_id

                should_compile = False
                if not self.metadata:
                    should_compile = True
                else:
                    for meta_key, meta_value in self.metadata.items():
                        key_string = meta_key.name if isinstance(meta_key, Name) else str(meta_key)
                        if key_string == target_name and meta_value.get("llvm"):
                            should_compile = True
                            break

                if should_compile:
                    discovery_targets[target_id] = current_term.var_value

            current_term = current_term.body

        return discovery_targets

    def get_curried_function(self, function_id: Name):
        if function_id not in self.compiled_functions:
            function_id = self.name_to_id_cache.get(function_id.name)

        if function_id is None or function_id not in self.compiled_functions:
            return None

        target_type = self.type_environment.get(function_id)
        if not target_type:
            return None

        target_llvm_type = to_llvm_type(target_type)
        param_types, return_type = self.lowerer.get_signature(target_llvm_type)

        def invoke_wrapper(accumulated_args: list[Any]):
            if len(accumulated_args) == len(param_types):
                assert function_id is not None
                return self.invoke(function_id, accumulated_args)
            else:
                return lambda next_arg: invoke_wrapper(accumulated_args + [next_arg])

        return invoke_wrapper([])

    def invoke(self, name_id: Name, arguments: list[Any]):
        target_type = self.type_environment.get(name_id)
        if not target_type:
            raise LLVMBackendError(f"type for {name_id} not found")

        target_llvm_type = to_llvm_type(target_type)
        param_types, return_type = self.lowerer.get_signature(target_llvm_type)

        return self.executor.execute(
            self.llvm_ir,
            sanitize_name(name_id),
            arguments,
            param_types,
            return_type,
        )
