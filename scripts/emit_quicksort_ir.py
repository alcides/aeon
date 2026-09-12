"""Emit identical checked quicksort programs with and without refinement hints.

PYTHONPATH=. python scripts/emit_quicksort_ir.py /tmp/quicksort-ir
Then run scripts/bench_llvm_quicksort.py on the CPU/CUDA benchmark host.
"""

import argparse
import json
from pathlib import Path

import llvmlite.binding as llvm
from loguru import logger

from aeon.compilation.compile import compile_and_link
from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.cuda.converter import CUDALLVMIRGenerator
from aeon.llvm.pipeline import MultiBackendPipeline
from aeon.llvm.utils import sanitize_name


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    logger.remove()
    source = Path(__file__).resolve().parents[1] / "examples/llvm/functional_quicksort.ae"
    _, core, _, metadata, _, errors = compile_and_link(str(source), is_main=True, is_main_hole=False)
    if errors:
        raise RuntimeError("\n".join(map(str, errors)))
    pipeline = MultiBackendPipeline(metadata)
    pipeline.compile(core)
    definitions = list(pipeline.compiled_functions_by_backend["cpu"].values())
    entry = next(sanitize_name(f.name) for f in definitions if f.name.name == "sort_into")
    args.directory.mkdir(parents=True, exist_ok=True)
    for backend, generator in (("cpu", CPULLVMIRGenerator), ("cuda", CUDALLVMIRGenerator)):
        for hints in (False, True):
            code = generator(use_refinements=hints).generate_ir(definitions)
            llvm.parse_assembly(code).verify()
            (args.directory / f"{backend}-{'hints' if hints else 'plain'}.ll").write_text(code)
    (args.directory / "manifest.json").write_text(json.dumps({"entry": entry, "source": source.name}, indent=2))
    print(f"Verified all four modules; entry point {entry}")


if __name__ == "__main__":
    main()
