from __future__ import annotations

from typing import Any, Dict

from loguru import logger

from aeon.core.terms import Term, Let, Rec
from aeon.llvm.core import LLVMPipeline, Backend, LLVMBackendError
from aeon.llvm.llvm_ast import LLVMFunction, LLVMTerm
from aeon.llvm.utils import sanitize_name, to_llvm_type
from aeon.llvm.cpu.executor import CPULLVMExecutionEngine
from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.utils.name import Name


class MultiBackendPipeline(LLVMPipeline):
    def __init__(self, metadata: Dict[Name, Any] | None = None):
        self.metadata = metadata or {}
        self.backends: Dict[str, Backend] = {}
        self.function_targets: Dict[Name, str] = {}
        self.compiled_functions_by_backend: Dict[str, Dict[Name, LLVMTerm]] = {}
        self.llvm_ir_by_backend: Dict[str, str] = {}
        self.type_environment: Dict[Name, Any] = {}
        self.name_to_id_cache: Dict[str, Name] = {}

        self.register_backend("cpu", Backend(CPULLVMExecutionEngine(), CPULLVMIRGenerator(), CPULLVMLowerer()))
        self.cuda_initialized = False

    def _initialize_cuda_backend(self):
        if not self.cuda_initialized:
            try:
                from aeon.llvm.cuda.lowerer import CUDALLVMLowerer
                from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
                from aeon.llvm.cuda.executor import CUDALLVMExecutionEngine

                cuda_backend = Backend(CUDALLVMExecutionEngine(), CUDALLVMIRGenerator(), CUDALLVMLowerer())
                self.register_backend("cuda", cuda_backend)
                self.cuda_initialized = True
            except Exception as e:
                logger.debug(f"CUDA backend initialization failed: {e}")

    def register_backend(self, name: str, backend: Backend):
        self.backends[name] = backend
        self.compiled_functions_by_backend[name] = {}
        self.llvm_ir_by_backend[name] = ""

    def _get_target_for_function(self, name: Name) -> str:
        meta = self.metadata.get(name)
        if meta is None:
            for meta_key, meta_value in self.metadata.items():
                key_string = meta_key.name if isinstance(meta_key, Name) else str(meta_key)
                if key_string == name.name:
                    meta = meta_value
                    break

        if meta and meta.get("gpu"):
            return meta.get("gpu_device", "cuda")
        return "cpu"

    def compile(self, program: Term):
        self._initialize_cuda_backend()
        discovered_targets = self._find_compilation_targets(program)

        for target_id, target_body in discovered_targets.items():
            target_name = self._get_target_for_function(target_id)
            if target_name not in self.backends:
                logger.warning(f"Backend {target_name} not found for function {target_id}. Falling back to cpu.")
                target_name = "cpu"

            self.function_targets[target_id] = target_name
            backend = self.backends[target_name]

            target_type = self.type_environment[target_id]
            target_llvm_type = to_llvm_type(target_type)

            env = {}
            for b_funcs in self.compiled_functions_by_backend.values():
                env.update(b_funcs)

            llvm_ast = backend.lowerer.lower(
                target_body,
                expected_type=target_llvm_type,
                type_env={fid: to_llvm_type(ty) for fid, ty in self.type_environment.items()},
                env=env,
            )

            if isinstance(llvm_ast, LLVMFunction):
                llvm_ast.name = target_id

            self.compiled_functions_by_backend[target_name][target_id] = llvm_ast

        for backend_name, backend in self.backends.items():  # generate ir
            funcs = list(self.compiled_functions_by_backend[backend_name].values())
            if funcs:
                self.llvm_ir_by_backend[backend_name] = backend.generator.generate_ir(funcs)
                logger.debug(f"Backend {backend_name} IR:\n{self.llvm_ir_by_backend[backend_name]}")

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
                for meta_key, meta_value in self.metadata.items():
                    key_string = meta_key.name if isinstance(meta_key, Name) else str(meta_key)
                    if key_string == target_name and (meta_value.get("llvm") or meta_value.get("gpu")):
                        should_compile = True
                        break

                if should_compile:
                    discovery_targets[target_id] = current_term.var_value

            current_term = current_term.body

        return discovery_targets

    def get_curried_function(self, function_id: Name):
        if function_id not in self.function_targets:
            function_id = self.name_to_id_cache.get(function_id.name)

        if function_id is None or function_id not in self.function_targets:
            return None

        target_name = self.function_targets[function_id]
        backend = self.backends[target_name]
        target_type = self.type_environment.get(function_id)

        target_llvm_type = to_llvm_type(target_type)
        param_types, return_type = backend.lowerer.get_signature(target_llvm_type)

        def invoke_wrapper(accumulated_args: list[Any]):
            if len(accumulated_args) == len(param_types):
                return self.invoke(function_id, accumulated_args)
            else:
                return lambda next_arg: invoke_wrapper(accumulated_args + [next_arg])

        return invoke_wrapper([])

    def invoke(self, name_id: Name, arguments: list[Any]):
        target_name = self.function_targets.get(name_id)
        if not target_name:  # try cache
            name_id = self.name_to_id_cache.get(name_id.name)
            target_name = self.function_targets.get(name_id)

        if not target_name:
            raise LLVMBackendError(f"target backend for {name_id} not found")

        backend = self.backends[target_name]
        target_type = self.type_environment.get(name_id)
        target_llvm_type = to_llvm_type(target_type)
        param_types, return_type = backend.lowerer.get_signature(target_llvm_type)

        return backend.executor.execute(
            self.llvm_ir_by_backend[target_name],
            sanitize_name(name_id),
            arguments,
            param_types,
            return_type,
        )
