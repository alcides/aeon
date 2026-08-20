from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Iterable, Sequence, TypeVar

from aeon.llvm.llvm_ast import (
    LLVMFunction,
    LLVMFunctionType,
    LLVMPointerType,
    LLVMVoidType,
    LLVMTerm,
    LLVMVectorCount,
    LLVMVectorFilter,
    LLVMVectorIMap,
    LLVMVectorMap,
    LLVMVectorReduce,
    LLVMVectorSize,
    LLVMVectorZipWith,
    LLVMVar,
    LLVMIntType,
    LLVMFloatType,
    LLVMDoubleType,
    LLVMLet,
    LLVMCast,
)
from aeon.llvm.utils import sanitize_name

TVectorOp = TypeVar("TVectorOp", LLVMVectorCount, LLVMVectorFilter, LLVMVectorReduce)


class CudaPlanAlgorithm(str, Enum):
    COUNT_TREE_I32 = "count_tree_i32"
    REDUCE_TREE = "reduce_tree"
    FILTER_COMPACT = "filter_compact"
    FILTER_SIZE_SCAN = "filter_size_scan"


class CudaResultKind(str, Enum):
    CALL = "call"
    SCALAR = "scalar"
    VECTOR = "vector"
    VOID = "void"


class CudaStepArgs(str, Enum):
    CALL = "call"
    PLANNED = "planned"
    TREE_REDUCE = "tree_reduce"
    PREFIX_SCAN = "prefix_scan"
    SCALAR_RESULT = "scalar_result"
    VECTOR_RESULT = "vector_result"


class CudaBufferName(str, Enum):
    COUNT_FLAGS = "count_flags"
    REDUCE_PING = "reduce_ping"
    REDUCE_WORK = "reduce_work"
    REDUCE_OUT = "reduce_out"
    FILTER_MASK = "filter_mask"
    FILTER_SCAN = "filter_scan"
    FILTER_OUT = "filter_out"


class CudaCommonKernelName(str, Enum):
    REDUCE_I32_STEP = "__aeon_reduce_i32_step"
    STORE_I32_RESULT = "__aeon_store_i32_result"
    STORE_I32_LAST = "__aeon_store_i32_last"
    SCAN_I32_INCLUSIVE_STEP = "__aeon_scan_i32_inclusive_step"


class CudaTempSpec(str, Enum):
    I32 = "temp_i32"
    F32 = "temp_f32"

    @property
    def pool_key(self) -> str:
        return self.value.removeprefix("temp_")

    @property
    def dtype(self) -> str:
        return "int32" if self is CudaTempSpec.I32 else "float32"


PLAN_ARRAYS_KEY = "__arrays__"
RESULT_BUFFER_DTYPE = "result"
PLAN_SIZE_DIM = "size"


def count_map_kernel_name(function: str) -> str:
    return f"{function}_count_map"


def reduce_copy_kernel_name(function: str) -> str:
    return f"{function}_reduce_copy"


def reduce_step_kernel_name(function: str) -> str:
    return f"{function}_reduce_step"


def reduce_finish_kernel_name(function: str) -> str:
    return f"{function}_reduce_finish"


def filter_mask_kernel_name(function: str) -> str:
    return f"{function}_filter_mask"


def filter_scatter_kernel_name(function: str) -> str:
    return f"{function}_filter_scatter"


@dataclass(frozen=True)
class CudaArgRef:
    kind: str
    name: str | int

    def to_dict(self) -> dict[str, Any]:
        return {"kind": self.kind, "name": self.name}


@dataclass(frozen=True)
class CudaBufferSpec:
    name: str
    dtype: str
    shape: tuple[str | int, ...]
    generation: int = 0

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "dtype": self.dtype,
            "shape": list(self.shape),
            "generation": self.generation,
        }


@dataclass(frozen=True)
class CudaResultSpec:
    kind: CudaResultKind | str
    buffer: str | None = None

    def to_dict(self) -> dict[str, Any]:
        kind = self.kind.value if isinstance(self.kind, CudaResultKind) else self.kind
        return {"kind": kind, "buffer": self.buffer}


@dataclass(frozen=True)
class CudaKernelStep:
    kernel: str
    args: CudaStepArgs | str | Sequence[Any] = CudaStepArgs.CALL
    block_size: int | None = None
    grid_size: int | None = None

    def to_dict(self) -> dict[str, Any]:
        args = self.args.value if isinstance(self.args, CudaStepArgs) else self.args
        return {
            "kernel": self.kernel,
            "args": args,
            "block_size": self.block_size,
            "grid_size": self.grid_size,
        }


@dataclass(frozen=True)
class CudaKernelPlan:
    function: str
    steps: tuple[CudaKernelStep, ...]
    buffers: tuple[CudaBufferSpec, ...] = ()
    args: tuple[CudaArgRef, ...] = ()
    result: CudaResultSpec = field(default_factory=lambda: CudaResultSpec(CudaResultKind.CALL))
    algorithm: CudaPlanAlgorithm | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "function": self.function,
            "steps": [step.to_dict() for step in self.steps],
            "buffers": [buf.to_dict() for buf in self.buffers],
            "args": [arg.to_dict() for arg in self.args],
            "result": self.result.to_dict(),
            "algorithm": self.algorithm.value if self.algorithm is not None else None,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> CudaKernelPlan:
        algorithm = data.get("algorithm")
        steps = tuple(
            CudaKernelStep(
                kernel=str(step.get("kernel")),
                args=step.get("args", CudaStepArgs.CALL),
                block_size=step.get("block_size"),
                grid_size=step.get("grid_size"),
            )
            for step in data.get("steps", [])
            if isinstance(step, dict) and step.get("kernel")
        )
        buffers = tuple(
            CudaBufferSpec(
                name=str(buf.get("name")),
                dtype=str(buf.get("dtype", "int32")),
                shape=tuple(buf.get("shape", [])),
                generation=int(buf.get("generation", 0)),
            )
            for buf in data.get("buffers", [])
            if isinstance(buf, dict) and buf.get("name")
        )
        args = tuple(
            CudaArgRef(kind=str(arg.get("kind", "arg")), name=arg.get("name", 0))
            for arg in data.get("args", [])
            if isinstance(arg, dict)
        )
        result_data = data.get("result", {})
        result = (
            CudaResultSpec(str(result_data.get("kind", CudaResultKind.CALL.value)), result_data.get("buffer"))
            if isinstance(result_data, dict)
            else CudaResultSpec(CudaResultKind.CALL)
        )
        return cls(
            function=str(data.get("function", "")),
            steps=steps,
            buffers=buffers,
            args=args,
            result=result,
            algorithm=CudaPlanAlgorithm(algorithm) if algorithm else None,
        )


class CudaKernelPlanner:
    def build(self, functions: Iterable[LLVMTerm]) -> dict[str, CudaKernelPlan]:
        plans: dict[str, CudaKernelPlan] = {}
        for func in functions:
            if not isinstance(func, LLVMFunction) or not func.name:
                continue
            fn_name = sanitize_name(func.name)
            plans[fn_name] = self._plan_function(fn_name, func)
        return plans

    def _plan_function(self, fn_name: str, func: LLVMFunction) -> CudaKernelPlan:
        count_term = self._find_count(func.body)
        if count_term is not None:
            return CudaKernelPlan(
                function=fn_name,
                args=tuple(CudaArgRef("arg", i) for i, _ in enumerate(func.arg_types)),
                buffers=(
                    CudaBufferSpec(CudaBufferName.COUNT_FLAGS.value, "int32", (PLAN_SIZE_DIM,), 0),
                    CudaBufferSpec(CudaBufferName.REDUCE_PING.value, "int32", (PLAN_SIZE_DIM,), 1),
                ),
                result=CudaResultSpec(CudaResultKind.SCALAR),
                steps=(
                    CudaKernelStep(kernel=count_map_kernel_name(fn_name), args=CudaStepArgs.PLANNED),
                    CudaKernelStep(kernel=CudaCommonKernelName.REDUCE_I32_STEP.value, args=CudaStepArgs.TREE_REDUCE),
                    CudaKernelStep(kernel=CudaCommonKernelName.STORE_I32_RESULT.value, args=CudaStepArgs.SCALAR_RESULT),
                ),
                algorithm=CudaPlanAlgorithm.COUNT_TREE_I32,
            )

        reduce_term = self._find_reduce(func.body)
        if reduce_term is not None:
            dtype = self._dtype_name(
                reduce_term.type.element_type if isinstance(reduce_term.type, LLVMPointerType) else reduce_term.type
            )
            is_vector_result = self._returns_vector(func)
            return CudaKernelPlan(
                function=fn_name,
                args=tuple(CudaArgRef("arg", i) for i, _ in enumerate(func.arg_types)),
                buffers=(
                    CudaBufferSpec(CudaBufferName.REDUCE_WORK.value, dtype, (PLAN_SIZE_DIM,), 0),
                    CudaBufferSpec(CudaBufferName.REDUCE_PING.value, dtype, (PLAN_SIZE_DIM,), 1),
                    CudaBufferSpec(CudaBufferName.REDUCE_OUT.value, dtype, (1,), 2),
                ),
                result=CudaResultSpec(
                    CudaResultKind.VECTOR if is_vector_result else CudaResultKind.SCALAR,
                    CudaBufferName.REDUCE_OUT.value if is_vector_result else None,
                ),
                steps=(
                    CudaKernelStep(kernel=reduce_copy_kernel_name(fn_name), args=CudaStepArgs.PLANNED),
                    CudaKernelStep(kernel=reduce_step_kernel_name(fn_name), args=CudaStepArgs.TREE_REDUCE),
                    CudaKernelStep(kernel=reduce_finish_kernel_name(fn_name), args=CudaStepArgs.VECTOR_RESULT),
                ),
                algorithm=CudaPlanAlgorithm.REDUCE_TREE,
            )

        filter_size_term = self._find_filter_size(func.body)
        if filter_size_term is not None and self._returns_scalar(func):
            return CudaKernelPlan(
                function=fn_name,
                args=tuple(CudaArgRef("arg", i) for i, _ in enumerate(func.arg_types)),
                buffers=(
                    CudaBufferSpec(CudaBufferName.FILTER_MASK.value, "int32", (PLAN_SIZE_DIM,), 0),
                    CudaBufferSpec(CudaBufferName.FILTER_SCAN.value, "int32", (PLAN_SIZE_DIM,), 1),
                ),
                result=CudaResultSpec(CudaResultKind.SCALAR),
                steps=(
                    CudaKernelStep(kernel=filter_mask_kernel_name(fn_name), args=CudaStepArgs.PLANNED),
                    CudaKernelStep(
                        kernel=CudaCommonKernelName.SCAN_I32_INCLUSIVE_STEP.value,
                        args=CudaStepArgs.PREFIX_SCAN,
                    ),
                    CudaKernelStep(kernel=CudaCommonKernelName.STORE_I32_LAST.value, args=CudaStepArgs.SCALAR_RESULT),
                ),
                algorithm=CudaPlanAlgorithm.FILTER_SIZE_SCAN,
            )

        filter_term = self._find_filter(func.body)
        if filter_term is not None and self._returns_vector(func):
            dtype = self._dtype_name(
                filter_term.type.element_type if isinstance(filter_term.type, LLVMPointerType) else filter_term.type
            )
            return CudaKernelPlan(
                function=fn_name,
                args=tuple(CudaArgRef("arg", i) for i, _ in enumerate(func.arg_types)),
                buffers=(
                    CudaBufferSpec(CudaBufferName.FILTER_MASK.value, "int32", (PLAN_SIZE_DIM,), 0),
                    CudaBufferSpec(CudaBufferName.FILTER_SCAN.value, "int32", (PLAN_SIZE_DIM,), 1),
                    CudaBufferSpec(CudaBufferName.FILTER_OUT.value, dtype, (PLAN_SIZE_DIM,), 2),
                ),
                result=CudaResultSpec(CudaResultKind.VECTOR, CudaBufferName.FILTER_OUT.value),
                steps=(
                    CudaKernelStep(kernel=filter_mask_kernel_name(fn_name), args=CudaStepArgs.PLANNED),
                    CudaKernelStep(
                        kernel=CudaCommonKernelName.SCAN_I32_INCLUSIVE_STEP.value,
                        args=CudaStepArgs.PREFIX_SCAN,
                    ),
                    CudaKernelStep(kernel=filter_scatter_kernel_name(fn_name), args=CudaStepArgs.PLANNED),
                ),
                algorithm=CudaPlanAlgorithm.FILTER_COMPACT,
            )

        buffers = tuple(self._discover_buffers(func.body))
        arg_refs = tuple(CudaArgRef("arg", i) for i, _ in enumerate(func.arg_types))
        result = CudaResultSpec(
            CudaResultKind.VECTOR
            if self._returns_vector(func)
            else CudaResultKind.SCALAR
            if self._returns_scalar(func)
            else CudaResultKind.VOID
        )
        return CudaKernelPlan(
            function=fn_name,
            args=arg_refs,
            buffers=buffers,
            result=result,
            steps=(CudaKernelStep(kernel=f"{fn_name}_kernel"),),
        )

    def _find_vector_op(self, term: LLVMTerm, op_type: type[TVectorOp]) -> TVectorOp | None:
        if isinstance(term, op_type):
            return term
        if isinstance(term, LLVMLet):
            return self._find_vector_op(term.var_value, op_type) or self._find_vector_op(term.body, op_type)
        if isinstance(term, LLVMCast):
            return self._find_vector_op(term.val, op_type)
        return None

    def _find_count(self, term: LLVMTerm) -> LLVMVectorCount | None:
        return self._find_vector_op(term, LLVMVectorCount)

    def _find_reduce(self, term: LLVMTerm) -> LLVMVectorReduce | None:
        return self._find_vector_op(term, LLVMVectorReduce)

    def _find_filter(self, term: LLVMTerm) -> LLVMVectorFilter | None:
        return self._find_vector_op(term, LLVMVectorFilter)

    def _find_filter_size(self, term: LLVMTerm, bindings: dict[str, LLVMTerm] | None = None) -> LLVMVectorFilter | None:
        bindings = dict(bindings or {})
        if isinstance(term, LLVMVectorSize):
            inner = term.v
            if isinstance(inner, LLVMVar):
                inner = bindings.get(sanitize_name(inner.name), inner)
            if isinstance(inner, LLVMCast):
                inner = inner.val
            if isinstance(inner, LLVMVectorFilter):
                return inner
        if isinstance(term, LLVMLet):
            next_bindings = dict(bindings)
            next_bindings[sanitize_name(term.var_name)] = term.var_value
            return self._find_filter_size(term.body, next_bindings) or self._find_filter_size(term.var_value, bindings)
        if isinstance(term, LLVMCast):
            return self._find_filter_size(term.val, bindings)
        return None

    def _dtype_name(self, ty: LLVMTerm | object) -> str:
        if isinstance(ty, LLVMIntType):
            return f"int{ty.bits}"
        if isinstance(ty, LLVMFloatType):
            return "float32"
        if isinstance(ty, LLVMDoubleType):
            return "float64"
        return "int32"

    def _returns_vector(self, func: LLVMFunction) -> bool:
        return isinstance(func.type, LLVMFunctionType) and isinstance(func.type.return_type, LLVMPointerType)

    def _returns_scalar(self, func: LLVMFunction) -> bool:
        return isinstance(func.type, LLVMFunctionType) and not isinstance(
            func.type.return_type, (LLVMPointerType, LLVMVoidType)
        )

    def _discover_buffers(self, term: LLVMTerm) -> list[CudaBufferSpec]:
        buffers: list[CudaBufferSpec] = []

        def walk(node: LLVMTerm):
            if isinstance(node, (LLVMVectorMap, LLVMVectorIMap, LLVMVectorZipWith)):
                buffers.append(
                    CudaBufferSpec(f"vector_tmp_{len(buffers)}", RESULT_BUFFER_DTYPE, (PLAN_SIZE_DIM,), len(buffers))
                )
            elif isinstance(node, LLVMVectorCount):
                buffers.append(CudaBufferSpec(f"count_flags_{len(buffers)}", "int32", (PLAN_SIZE_DIM,), len(buffers)))
                walk(node.v)
            elif isinstance(node, LLVMVectorReduce):
                buffers.append(
                    CudaBufferSpec(f"reduce_work_{len(buffers)}", RESULT_BUFFER_DTYPE, (PLAN_SIZE_DIM,), len(buffers))
                )
                walk(node.v)
                walk(node.initial)
            elif isinstance(node, LLVMVectorFilter):
                generation = len(buffers)
                buffers.append(CudaBufferSpec(f"filter_mask_{generation}", "int32", (PLAN_SIZE_DIM,), generation))
                buffers.append(
                    CudaBufferSpec(f"filter_out_{generation}", RESULT_BUFFER_DTYPE, (PLAN_SIZE_DIM,), generation)
                )
                walk(node.v)
            elif isinstance(node, LLVMVectorSize):
                walk(node.v)
            elif isinstance(node, LLVMLet):
                walk(node.var_value)
                walk(node.body)
            elif isinstance(node, LLVMCast):
                walk(node.val)

        walk(term)
        return buffers
