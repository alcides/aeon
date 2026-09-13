# Knapsack GA as one LLVM / CUDA kernel
#
# `KnapsackGA` compiles a 0-1 knapsack genetic algorithm into a **single**
# LLVM function whose body contains the full generation loop. On CUDA that
# function is launched once as `knapsack_ga__kernel`; the host uploads
# buffers, launches, and synchronises only when the kernel finishes.
#
# Default workload (see `examples/llvm/gpu/knapsack_ga.ae`):
#
# | Parameter | Value |
# |-----------|------:|
# | Items | 1000 |
# | Population | 100 |
# | Generations | 14_500 (≈5 min on the calibration GPU; recalibrate with the bench script) |
#
# Calibrate with:
#
# ```bash
# uv run python scripts/bench_knapsack_ga_gpu.py --gpu --target-seconds 300
# ```
#
# Source: `aeon/libraries/KnapsackGA.ae`, IR builder
# `aeon/llvm/kernels/knapsack_ga_ir.py`, binding `aeon/bindings/knapsack_ga.py`.
