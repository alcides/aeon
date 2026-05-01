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

    def _get_preferred_backend(self, name: Name) -> str:
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
        compilable_defs = self._find_compilable_definitions(program)

        for func_id, func_body in compilable_defs.items():
            preferred_backend = self._get_preferred_backend(func_id)

            backends_to_try = []
            if preferred_backend in self.backends and preferred_backend != "cpu":
                backends_to_try.append(preferred_backend)
            backends_to_try.append("cpu")

            successful_backends = []

            for backend_name in backends_to_try:
                try:
                    backend = self.backends[backend_name]

                    func_type = self.type_environment[func_id]
                    func_llvm_type = to_llvm_type(func_type)

                    env = {}
                    for b_funcs in self.compiled_functions_by_backend.values():
                        env.update(b_funcs)

                    llvm_ast = backend.lowerer.lower(
                        func_body,
                        expected_type=func_llvm_type,
                        type_env={fid: to_llvm_type(ty) for fid, ty in self.type_environment.items()},
                        env=env,
                    )

                    if isinstance(llvm_ast, LLVMFunction):
                        llvm_ast.name = func_id

                    self.compiled_functions_by_backend[backend_name][func_id] = llvm_ast
                    successful_backends.append(backend_name)
                except Exception as e:
                    logger.debug(f"Failed to compile {func_id} for {backend_name}: {e}")

            if successful_backends:
                self.function_targets[func_id] = successful_backends
            else:
                logger.warning(f"All LLVM compilations failed for {func_id}. Falling back to native python.")

    def _find_compilable_definitions(self, term: Term) -> Dict[Name, Term]:
        compilable_defs = {}
        current_term = term

        while isinstance(current_term, (Let, Rec)):
            if isinstance(current_term, Rec):
                func_id = current_term.var_name
                func_name = func_id.name

                self.type_environment[func_id] = current_term.var_type
                self.name_to_id_cache[func_name] = func_id

                should_compile = False
                for meta_key, meta_value in self.metadata.items():
                    key_string = meta_key.name if isinstance(meta_key, Name) else str(meta_key)
                    if key_string == func_name and (meta_value.get("cpu") or meta_value.get("gpu")):
                        should_compile = True
                        break

                if should_compile:
                    compilable_defs[func_id] = current_term.var_value

            current_term = current_term.body

        return compilable_defs

    def get_curried_function(self, function_id: Name, native_fallback: Any = None):
        try:
            if function_id not in self.function_targets:
                function_id = self.name_to_id_cache.get(function_id.name)

            if function_id is None or function_id not in self.function_targets:
                return native_fallback

            backend_names = [b for b in self.function_targets[function_id] if b not in self.disabled_backends]
            if not backend_names:
                return native_fallback

            primary_backend = backend_names[0]
            backend = self.backends.get(primary_backend)
            if not backend:
                return native_fallback

            func_type = self.type_environment.get(function_id)

            func_llvm_type = to_llvm_type(func_type)
            param_types, _ = backend.lowerer.get_signature(func_llvm_type)

            def invoke_wrapper(accumulated_args: list[Any]):
                if len(accumulated_args) == len(param_types):
                    return self.invoke(function_id, accumulated_args, native_fallback)
                else:
                    return lambda next_arg: invoke_wrapper(accumulated_args + [next_arg])

            return invoke_wrapper([])
        except Exception as e:
            logger.debug(f"Failed to create LLVM curried function for {function_id}: {e}")
            return native_fallback

    def invoke(self, name: Name, arguments: list[Any], native_fallback: Any = None):
        resolved_id = self._resolve_id(name)
        potential_backends = self.function_targets.get(resolved_id) if resolved_id else None

        if not potential_backends or not (
            active_backends := [b for b in potential_backends if b not in self.disabled_backends]
        ):
            return self._handle_fallback(native_fallback, arguments, resolved_id or name)

        last_error = None
        target_type = self.type_environment.get(resolved_id)
        llvm_type = to_llvm_type(target_type) if target_type else None

        for backend_name in active_backends:
            if not (backend := self.backends.get(backend_name)):
                continue

            if not self._generate_ir_if_needed(backend_name, backend):
                continue

            try:
                params, ret = backend.lowerer.get_signature(llvm_type)

                return backend.executor.execute(
                    self.llvm_ir_by_backend[backend_name],
                    sanitize_name(resolved_id),
                    arguments,
                    params,
                    ret,
                )
            except Exception as e:
                logger.debug(f"Execution failed on {backend_name} for {resolved_id}: {e}. Disabling backend.")
                self.disabled_backends.add(backend_name)
                last_error = e

        return self._handle_fallback(native_fallback, arguments, resolved_id, last_error)

    def _resolve_id(self, name_id: Name) -> Name | None:
        if name_id in self.function_targets:
            return name_id
        return self.name_to_id_cache.get(name_id.name)

    def _generate_ir_if_needed(self, backend_name: str, backend: Backend) -> bool:
        if self.llvm_ir_by_backend.get(backend_name):
            return True

        funcs = list(self.compiled_functions_by_backend[backend_name].values())
        if not funcs:
            return False

        try:
            self.llvm_ir_by_backend[backend_name] = backend.generator.generate_ir(funcs)
            logger.debug(f"Backend {backend_name} IR:\n{self.llvm_ir_by_backend[backend_name]}")
            return True
        except Exception as e:
            logger.warning(f"IR generation failed for {backend_name}: {e}. Disabling backend.")
            self.disabled_backends.add(backend_name)
            return False

    def _handle_fallback(self, fallback: Any, args: list[Any], name_id: Name, error: Exception | None = None):
        if fallback:
            return self._invoke_native(fallback, args)

        msg = f"All executions failed for {name_id}" if error else f"target backend for {name_id} not found"
        raise LLVMBackendError(f"{msg}. Last error: {error}" if error else msg)

    def _invoke_native(self, native_func: Any, args: list[Any]) -> Any:
        res = native_func
        for arg in args:
            if callable(res):
                res = res(arg)
            else:
                raise LLVMBackendError("Native fallback is not callable with provided arguments.")
        return res
