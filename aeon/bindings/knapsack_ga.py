"""Run the knapsack GA as one LLVM/CUDA kernel (no mid-run host sync)."""

from __future__ import annotations

import ctypes
import random
from typing import Sequence

import llvmlite.binding as llvm

from aeon.bindings.binding_utils import curried
from aeon.llvm.kernels.knapsack_ga_ir import knapsack_ga_ir
from aeon.llvm.optimization import optimize_module


def _init_population(n_items: int, pop_size: int, seed: int) -> list[int]:
    """Sparse random bitstrings so early generations contain feasible packs."""
    rng = random.Random(seed)
    # Target ~capacity/mean_weight items selected; use p=0.15 as a robust default.
    return [1 if rng.random() < 0.15 else 0 for _ in range(pop_size * n_items)]


def _as_i32_array(values: Sequence[int]) -> ctypes.Array:
    return (ctypes.c_int32 * len(values))(*[int(v) for v in values])


def run_cpu(
    weights: Sequence[int],
    values: Sequence[int],
    n_items: int,
    capacity: int,
    pop_size: int,
    generations: int,
    seed: int,
) -> int:
    """Execute the GA on the host via MCJIT (same IR loops as the GPU path)."""
    assert len(weights) >= n_items and len(values) >= n_items
    pop = _init_population(n_items, pop_size, seed)
    next_pop = [0] * (pop_size * n_items)
    fitness = [0] * pop_size

    llvm.initialize_native_target()
    llvm.initialize_native_asmprinter()
    ir = knapsack_ga_ir(nvptx=False)
    mod = llvm.parse_assembly(ir)
    mod.verify()
    tm = llvm.Target.from_default_triple().create_target_machine()
    optimize_module(mod, tm, 3)
    with llvm.create_mcjit_compiler(mod, tm) as engine:
        engine.finalize_object()
        addr = engine.get_function_address("knapsack_ga")
        cfunc = ctypes.CFUNCTYPE(
            ctypes.c_int32,
            ctypes.POINTER(ctypes.c_int32),
            ctypes.POINTER(ctypes.c_int32),
            ctypes.POINTER(ctypes.c_int32),
            ctypes.POINTER(ctypes.c_int32),
            ctypes.POINTER(ctypes.c_int32),
            ctypes.c_int32,
            ctypes.c_int32,
            ctypes.c_int32,
            ctypes.c_int32,
            ctypes.c_int32,
        )(addr)
        w = _as_i32_array(weights[:n_items])
        v = _as_i32_array(values[:n_items])
        p = _as_i32_array(pop)
        npop = _as_i32_array(next_pop)
        fit = _as_i32_array(fitness)
        return int(
            cfunc(
                w,
                v,
                p,
                npop,
                fit,
                n_items,
                capacity,
                pop_size,
                generations,
                seed,
            )
        )


def run_gpu(
    weights: Sequence[int],
    values: Sequence[int],
    n_items: int,
    capacity: int,
    pop_size: int,
    generations: int,
    seed: int,
) -> int:
    """Upload once, launch one kernel for all generations, sync once, return best."""
    from aeon.llvm.cuda.executor import CUDAExecutionEngine
    from aeon.llvm.llvm_ast import LLVMInt, LLVMPointerType

    assert len(weights) >= n_items and len(values) >= n_items
    pop = _init_population(n_items, pop_size, seed)
    next_pop = [0] * (pop_size * n_items)
    fitness = [0] * pop_size
    ir = knapsack_ga_ir(nvptx=True)
    engine = CUDAExecutionEngine()
    i32p = LLVMPointerType(LLVMInt)
    return int(
        engine.execute(
            ir,
            "knapsack_ga",
            [
                list(weights[:n_items]),
                list(values[:n_items]),
                pop,
                next_pop,
                fitness,
                n_items,
                capacity,
                pop_size,
                generations,
                seed,
            ],
            [i32p, i32p, i32p, i32p, i32p, LLVMInt, LLVMInt, LLVMInt, LLVMInt, LLVMInt],
            LLVMInt,
        )
    )


@curried
def run_cpu_aeon(
    weights: list[int],
    values: list[int],
    n_items: int,
    capacity: int,
    pop_size: int,
    generations: int,
    seed: int,
) -> int:
    return run_cpu(weights, values, n_items, capacity, pop_size, generations, seed)


@curried
def run_gpu_aeon(
    weights: list[int],
    values: list[int],
    n_items: int,
    capacity: int,
    pop_size: int,
    generations: int,
    seed: int,
) -> int:
    return run_gpu(weights, values, n_items, capacity, pop_size, generations, seed)


def make_random_instance(n_items: int, seed: int = 1) -> tuple[list[int], list[int], int]:
    rng = random.Random(seed)
    weights = [rng.randint(1, 50) for _ in range(n_items)]
    values = [rng.randint(1, 100) for _ in range(n_items)]
    capacity = max(1, sum(weights) // 3)
    return weights, values, capacity


def run_random_cpu(n_items: int, pop_size: int, generations: int, seed: int) -> int:
    weights, values, capacity = make_random_instance(n_items, seed)
    return run_cpu(weights, values, n_items, capacity, pop_size, generations, seed)


def run_random_gpu(n_items: int, pop_size: int, generations: int, seed: int) -> int:
    weights, values, capacity = make_random_instance(n_items, seed)
    return run_gpu(weights, values, n_items, capacity, pop_size, generations, seed)


@curried
def run_random_cpu_aeon(n_items: int, pop_size: int, generations: int, seed: int) -> int:
    return run_random_cpu(n_items, pop_size, generations, seed)


@curried
def run_random_gpu_aeon(n_items: int, pop_size: int, generations: int, seed: int) -> int:
    return run_random_gpu(n_items, pop_size, generations, seed)
