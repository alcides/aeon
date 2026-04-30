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
    def __init__(self, metadata: Dict[Name, Any] | None = None, debug: bool = False):
        self.metadata = metadata or {}
        self.backends: Dict[str, Backend] = {}
        self.function_targets: Dict[Name, list[str]] = {}
        self.compiled_functions_by_backend: Dict[str, Dict[Name, LLVMTerm]] = {}
        self.llvm_ir_by_backend: Dict[str, str] = {}
        self.type_environment: Dict[Name, Any] = {}
        self.name_to_id_cache: Dict[str, Name] = {}
        self.disabled_backends: set[str] = set()
        self.debug = debug

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
            except Exception as e:
                logger.debug(f"CUDA backend initialization failed: {e}")
                self.disabled_backends.add("cuda")
            finally:
                self.cuda_initialized = True

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

            targets_to_try = []
            if target_name in self.backends and target_name != "cpu":
                targets_to_try.append(target_name)
            targets_to_try.append("cpu")

            successful_targets = []

            for current_target in targets_to_try:
                try:
                    backend = self.backends[current_target]

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

                    self.compiled_functions_by_backend[current_target][target_id] = llvm_ast
                    successful_targets.append(current_target)
                except Exception as e:
                    logger.debug(f"Failed to compile {target_id} for {current_target}: {e}")

            if successful_targets:
                self.function_targets[target_id] = successful_targets
            else:
                logger.debug(f"All LLVM compilations failed for {target_id}. Falling back to native python.")

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
                    if key_string == target_name and (meta_value.get("cpu") or meta_value.get("gpu")):
                        should_compile = True
                        break

                if should_compile:
                    discovery_targets[target_id] = current_term.var_value

            current_term = current_term.body

        return discovery_targets

    def get_curried_function(self, function_id: Name, native_fallback: Any = None):
        try:
            if function_id not in self.function_targets:
                function_id = self.name_to_id_cache.get(function_id.name)

            if function_id is None or function_id not in self.function_targets:
                return native_fallback

            target_names = [t for t in self.function_targets[function_id] if t not in self.disabled_backends]
            if not target_names:
                return native_fallback

            first_target = target_names[0]
            backend = self.backends.get(first_target)
            if not backend:
                return native_fallback

            target_type = self.type_environment.get(function_id)

            target_llvm_type = to_llvm_type(target_type)
            param_types, _ = backend.lowerer.get_signature(target_llvm_type)

            def invoke_wrapper(accumulated_args: list[Any]):
                if len(accumulated_args) == len(param_types):
                    return self.invoke(function_id, accumulated_args, native_fallback)
                else:
                    return lambda next_arg: invoke_wrapper(accumulated_args + [next_arg])

            return invoke_wrapper([])
        except Exception as e:
            logger.debug(f"Failed to create LLVM curried function for {function_id}: {e}")
            return native_fallback

    def invoke(self, name_id: Name, arguments: list[Any], native_fallback: Any = None):
        target_names = self.function_targets.get(name_id)
        if not target_names:  # try cache
            name_id = self.name_to_id_cache.get(name_id.name)
            target_names = self.function_targets.get(name_id)

        if not target_names:
            if native_fallback:
                return self._invoke_native(native_fallback, arguments)
            raise LLVMBackendError(f"target backend for {name_id} not found")

        active_targets = [t for t in target_names if t not in self.disabled_backends]
        if not active_targets and native_fallback:
            return self._invoke_native(native_fallback, arguments)

        last_exception = None

        for target_name in active_targets:
            backend = self.backends.get(target_name)
            if not backend:
                continue

            if not self.llvm_ir_by_backend.get(target_name):
                funcs = list(self.compiled_functions_by_backend[target_name].values())
                if funcs:
                    try:
                        self.llvm_ir_by_backend[target_name] = backend.generator.generate_ir(funcs)
                        logger.debug(f"Backend {target_name} IR:\n{self.llvm_ir_by_backend[target_name]}")
                    except Exception as e:
                        logger.debug(f"IR generation failed for {target_name}: {e}. Disabling backend.")
                        self.disabled_backends.add(target_name)
                        continue
                else:
                    continue

            try:
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
            except Exception as e:
                logger.debug(f"Execution failed on {target_name} for {name_id}: {e}. Disabling backend.")
                last_exception = e
                self.disabled_backends.add(target_name)

        if native_fallback:
            return self._invoke_native(native_fallback, arguments)

        raise LLVMBackendError(f"All executions failed for {name_id}. Last error: {last_exception}")

    def _invoke_native(self, native_func: Any, args: list[Any]) -> Any:
        res = native_func
        for arg in args:
            if callable(res):
                res = res(arg)
            else:
                raise LLVMBackendError("Native fallback is not callable with provided arguments.")
        return res
