from __future__ import annotations

from enum import Enum
from typing import Any, Mapping


class LLVMBackendName(str, Enum):
    CPU = "cpu"
    CUDA = "cuda"


class LLVMMetadataKey(str, Enum):
    CPU_ENABLED = "cpu"
    CPU_OPT_LEVEL = "cpu_opt_level"
    GPU_ENABLED = "gpu"
    GPU_DEVICE = "gpu_device"
    GPU_OPT_LEVEL = "gpu_opt_level"
    GPU_DEBUG = "gpu_debug"
    GPU_BLOCK_SIZE = "gpu_block_size"
    GPU_ARCH = "gpu_arch"
    GPU_KERNEL_PLAN = "gpu_kernel_plan"
    GPU_NO_DEVICE_ALLOC = "gpu_no_device_alloc"
    SIZE = "size"


class VectorOperation(str, Enum):
    MAP = "map"
    REDUCE = "reduce"
    IMAP = "imap"
    FILTER = "filter"
    ZIP_WITH = "zipWith"
    COUNT = "count"
    SIZE = "size"


VECTOR_OPERATION_NAMES: frozenset[str] = frozenset(op.value for op in VectorOperation)


def metadata_get(metadata: Mapping[str, Any], key: LLVMMetadataKey, default: Any = None) -> Any:
    return metadata.get(key.value, default)


def metadata_has(metadata: Mapping[str, Any], key: LLVMMetadataKey) -> bool:
    return key.value in metadata
