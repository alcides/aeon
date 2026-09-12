"""Benchmark emitted quicksort IR; requires only llvmlite, plus CUDA for --gpu.

python scripts/bench_llvm_quicksort.py /tmp/quicksort-ir --gpu > results.json
Compilation, device transfers and correctness checks are outside timed regions.
The GPU runs the same sequential algorithm in one thread, not a parallel sort.
"""

from __future__ import annotations

import argparse
import ctypes as c
import json
from pathlib import Path
import platform
import random
import statistics
import time

import llvmlite
import llvmlite.binding as llvm

VARIANTS = [("LLVM-O0", "plain", 0), ("LLVM-O3", "plain", 3), ("LLVM-O3+refinements", "hints", 3)]


def optimize(module, tm, level):
    module.verify()
    if level:
        with llvm.create_pipeline_tuning_options(speed_level=level) as opts:
            with llvm.create_pass_builder(tm, opts) as builder:
                with builder.getModulePassManager() as passes:
                    passes.run(module, builder)
    module.verify()


class CPU:
    def __init__(self, ir, entry, level):
        llvm.initialize_native_target()
        llvm.initialize_native_asmprinter()
        tm = llvm.Target.from_default_triple().create_target_machine()
        module = llvm.parse_assembly(ir)
        module.triple = llvm.get_default_triple()
        module.data_layout = str(tm.target_data)
        optimize(module, tm, level)
        self.engine = llvm.create_mcjit_compiler(module, tm)
        self.engine.finalize_object()
        pointer = self.engine.get_function_address(entry)
        if not pointer:
            raise RuntimeError(f"Missing entry point {entry}")
        self.function = c.CFUNCTYPE(None, c.POINTER(c.c_int32), c.POINTER(c.c_int32), c.c_int32)(pointer)

    def run(self, source, output, n, batch):
        start = time.perf_counter_ns()
        for _ in range(batch):
            self.function(source, output, n)
        return (time.perf_counter_ns() - start) / batch / 1e6


class CUDA:
    def __init__(self):
        self.lib = c.CDLL("libcuda.so.1")
        self.call("cuInit", 0)
        device, self.context = c.c_int(), c.c_void_p()
        self.call("cuDeviceGet", c.byref(device), 0)
        self.call("cuCtxCreate_v2", c.byref(self.context), 0, device)
        self.device = device
        self.call("cuCtxSetCurrent", self.context)
        self.call("cuCtxSetLimit", 0, c.c_size_t(65536))
        self.call("cuCtxSetLimit", 2, c.c_size_t(64 << 20))
        major, minor = c.c_int(), c.c_int()
        self.call("cuDeviceGetAttribute", c.byref(major), 75, device)
        self.call("cuDeviceGetAttribute", c.byref(minor), 76, device)
        self.arch = f"sm_{major.value}{minor.value}"
        name = c.create_string_buffer(256)
        self.call("cuDeviceGetName", name, 256, device)
        self.name = name.value.decode()
        self.modules = []
        self.events = []
        for _ in range(2):
            event = c.c_void_p()
            self.call("cuEventCreate", c.byref(event), 0)
            self.events.append(event)

    def call(self, name, *args):
        result = getattr(self.lib, name)(*args)
        if result:
            error = c.c_char_p()
            self.lib.cuGetErrorString(result, c.byref(error))
            raise RuntimeError(f"{name}: {result}: {error.value!r}")

    def compile(self, ir, entry, level):
        llvm.initialize_all_targets()
        llvm.initialize_all_asmprinters()
        tm = llvm.Target.from_triple("nvptx64-nvidia-cuda").create_target_machine(cpu=self.arch)
        module = llvm.parse_assembly(ir)
        module.data_layout = str(tm.target_data)
        optimize(module, tm, level)
        ptx = tm.emit_assembly(module).encode() + b"\0"
        link = c.c_void_p()
        self.call("cuLinkCreate_v2", 0, None, None, c.byref(link))
        try:
            self.call("cuLinkAddData_v2", link, 1, c.c_char_p(ptx), c.c_size_t(len(ptx)), b"sort.ptx", 0, None, None)
            libraries = [Path("/usr/local/cuda/lib64/libcudadevrt.a"), Path("/usr/lib/x86_64-linux-gnu/libcudadevrt.a")]
            library = next((p for p in libraries if p.exists()), None)
            if library is None:
                raise RuntimeError("libcudadevrt.a is required for device malloc/free")
            self.call("cuLinkAddFile_v2", link, 4, str(library).encode(), 0, None, None)
            cubin, size = c.c_void_p(), c.c_size_t()
            self.call("cuLinkComplete", link, c.byref(cubin), c.byref(size))
            loaded = c.c_void_p()
            self.call("cuModuleLoadData", c.byref(loaded), cubin)
            self.modules.append(loaded)
        finally:
            self.call("cuLinkDestroy", link)
        function = c.c_void_p()
        self.call("cuModuleGetFunction", c.byref(function), loaded, (entry + "__kernel").encode())
        return function

    def alloc(self, size):
        pointer = c.c_uint64()
        self.call("cuMemAlloc_v2", c.byref(pointer), c.c_size_t(max(4, size)))
        return pointer

    def run(self, function, source, output, n, batch):
        length = c.c_int32(n)
        params = (c.c_void_p * 3)(c.addressof(source), c.addressof(output), c.addressof(length))
        self.call("cuEventRecord", self.events[0], None)
        for _ in range(batch):
            self.call("cuLaunchKernel", function, 1, 1, 1, 1, 1, 1, 0, None, params, None)
        self.call("cuEventRecord", self.events[1], None)
        self.call("cuEventSynchronize", self.events[1])
        elapsed = c.c_float()
        self.call("cuEventElapsedTime", c.byref(elapsed), self.events[0], self.events[1])
        return elapsed.value / batch

    def close(self):
        for module in self.modules:
            self.call("cuModuleUnload", module)
        for event in self.events:
            self.call("cuEventDestroy_v2", event)
        self.call("cuCtxDestroy_v2", self.context)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--gpu", action="store_true")
    parser.add_argument("--sizes", nargs="+", type=int, default=[256, 1024])
    parser.add_argument("--repeats", type=int, default=15)
    parser.add_argument("--batch", type=int, default=10)
    args = parser.parse_args()
    if min(args.sizes) < 0 or max(args.sizes) > 32768 or args.repeats < 1 or args.batch < 1:
        parser.error("sizes must be 0..32768; repeats and batch must be positive")
    manifest = json.loads((args.directory / "manifest.json").read_text())
    cpu = {
        name: CPU((args.directory / f"cpu-{hints}.ll").read_text(), manifest["entry"], level)
        for name, hints, level in VARIANTS
    }
    gpu = CUDA() if args.gpu else None
    gpu_functions = (
        {
            name: gpu.compile((args.directory / f"cuda-{hints}.ll").read_text(), manifest["entry"], level)
            for name, hints, level in VARIANTS
        }
        if gpu
        else {}
    )
    rows = []
    rng = random.Random(20260910)
    try:
        for n in args.sizes:
            original = [rng.randrange(-(1 << 30), 1 << 30) for _ in range(n)]
            expected = sorted(original)
            source = (c.c_int32 * n)(*original)
            output = (c.c_int32 * n)()
            d_source = gpu.alloc(c.sizeof(source)) if gpu else None
            d_output = gpu.alloc(c.sizeof(output)) if gpu else None
            if gpu:
                gpu.call("cuMemcpyHtoD_v2", d_source, source, c.c_size_t(c.sizeof(source)))
            try:
                for backend in ["cpu", "gpu"] if gpu else ["cpu"]:
                    samples = {name: [] for name, _, _ in VARIANTS}
                    for trial in range(-3, args.repeats):
                        order = list(samples)
                        rng.shuffle(order)
                        for name in order:
                            if backend == "cpu":
                                ms = cpu[name].run(source, output, n, args.batch)
                            else:
                                ms = gpu.run(gpu_functions[name], d_source, d_output, n, args.batch)
                                gpu.call("cuMemcpyDtoH_v2", output, d_output, c.c_size_t(c.sizeof(output)))
                                gpu.call("cuMemcpyDtoH_v2", source, d_source, c.c_size_t(c.sizeof(source)))
                            if list(output) != expected or list(source) != original:
                                raise AssertionError(f"Incorrect output or mutated input: {backend}, {name}, n={n}")
                            if trial >= 0:
                                samples[name].append(ms)
                    rows.append(
                        {
                            "backend": backend,
                            "n": n,
                            "samples_ms": samples,
                            "median_ms": {name: statistics.median(v) for name, v in samples.items()},
                        }
                    )
            finally:
                if gpu:
                    gpu.call("cuMemFree_v2", d_source)
                    gpu.call("cuMemFree_v2", d_output)
    finally:
        if gpu:
            gpu.close()
    print(
        json.dumps(
            {
                "platform": platform.platform(),
                "cpu": str(llvm.get_host_cpu_name()),
                "llvmlite": llvmlite.__version__,
                "llvm": llvm.llvm_version_info,
                "gpu": gpu.name if gpu else None,
                "repeats": args.repeats,
                "batch": args.batch,
                "rows": rows,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
