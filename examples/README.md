# Examples

Paper-based programs and named benchmark collections live in
[`benchmarks/<benchmark_name>/`](benchmarks/README.md), including Synquid, PSB2,
MBPP, SRBench, and the functional-synthesis paper artifacts. Each suite retains
its specifications, reference variants, data, and provenance.

The complete [non-benchmark inventory](ORGANIZATION.md) lists local demos, tutorials,
exercises, regression cases, and examples with uncertain benchmark provenance.
The [local synthesis overview](synthesis/README.md) identifies the larger examples
and groups control policies, puzzles, and level-design/assignment examples under
`synthesis/control/`, `synthesis/puzzle/`, and `synthesis/leveldesign/`.
ARC- and Fandango-inspired tasks live in `benchmarks/arc/`
and `benchmarks/fandango/`, with their adaptation scope documented there.
The 11 local microbenchmarks directly under `benchmarks/` also await a placement decision.

Run commands from the repository root. `bash run_examples.sh` recursively checks
`.ae` programs, runs designated property/test examples, and accounts for expected
negative cases. Benchmark checking does not run synthesis searches. See
[benchmark usage](../docs/benchmarks.md) for individual synthesis commands.
