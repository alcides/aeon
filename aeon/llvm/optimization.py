"""Run the same LLVM optimization pipeline for native CPU and NVPTX code."""

import llvmlite.binding as llvm


def optimize_module(module, target_machine, opt_level: int = 3) -> None:
    if not 0 <= opt_level <= 3:
        raise ValueError("LLVM optimization level must be between 0 and 3")
    module.verify()
    if opt_level:
        with llvm.create_pipeline_tuning_options(speed_level=opt_level) as options:
            with llvm.create_pass_builder(target_machine, options) as builder:
                with builder.getModulePassManager() as passes:
                    passes.run(module, builder)
    module.verify()
