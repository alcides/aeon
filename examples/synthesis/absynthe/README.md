# Absynthe SyGuS string benchmarks

This directory ports the complete 27-file string benchmark dataset from the
[official Absynthe artifact](https://github.com/ku-progsys/absynthe), revision
`d752fa4f3583d4f438021b92bd97983202a4dd17`. The original project provides
`.sl` inputs but no parser; Aeon reads their typed SLIA SyGuS subset through
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

`artifact.json` records the provenance checksums, every fixture's number of
constraints, and the artifact's Table 1 runner parameters: 11 baseline runs,
one run each without template inference and small-expression caching, and a
600-second timeout. It also preserves the non-default abstract specifications,
timeouts, and unsupported conditional tasks from `test/sygus_bench.rb`.
