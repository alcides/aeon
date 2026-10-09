# Absynthe SyGuS string benchmarks

This directory ports a representative, executable subset of the string
benchmarks distributed with [Absynthe](https://github.com/ngsankha/absynthe-rust)
(commit `54613a6`).  The original project provides `.sl` inputs but no parser;
Aeon reads their typed SLIA SyGuS subset through
`aeon.synthesis.benchmarks.absynthe`.

The reader supports the full DSL used by the corpus: strings, integers,
booleans, conditionals, concatenation, replacement, substring/character
access, integer conversion/arithmetic, length/index lookup, and string
predicates.  Its `Benchmark.fitness` reports the count of violated example
constraints, so an exact candidate has fitness `0`.

These files are data fixtures, not Aeon programs.  They can be used by a
synthesis backend as follows:

```python
from aeon.synthesis.benchmarks.absynthe import load_benchmark, parse_expression

benchmark = load_benchmark("examples/synthesis/absynthe/bikes.sl")
candidate = parse_expression("(str.substr name 0 (- (str.len name) 3))")
assert benchmark.fitness(candidate) == 0
```

The curated set covers the single-input extraction tasks (`bikes`, `phone`,
`dr-name`) and both one- and two-input name formatting variants.  The upstream
format is parsed generically, so the remaining Absynthe `.sl` files can be
loaded without format-specific code.
