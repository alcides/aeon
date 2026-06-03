# Benchmarks

Aeon ships with a large collection of programs that exercise the synthesizer
(`?hole` filling) and the verifier. They double as a regression suite (a subset
runs in CI via `run_examples.sh`) and as a catalogue of what liquid-type-guided
synthesis can express. This page is a map of what is available, where it lives,
and how to run it.

For the synthesizer backends these benchmarks target (`gp`, `enumerative`,
`tdsyn`, `synquid`, ...), see [synthesizers.md](synthesizers.md).

## How to run

A single benchmark:

```bash
# Synthesize a hole (genetic programming, 30s budget):
uv run python -m aeon --budget 30 -s gp examples/synthesis/nqueens.ae

# Type-check only, without synthesis (fast; good for parser/elaboration checks):
uv run python -m aeon -n examples/synthesis/smt/abbots_puzzle.ae
```

The whole CI example suite (synthesis + verification + library examples), in
parallel across all cores:

```bash
bash run_examples.sh
```

`run_examples.sh` treats exit code `0` as success, `2` as "no solution found
within the budget, but OK", and anything else as a hard failure.

## Suites at a glance

| Suite | Location | Count | What it is |
|---|---|--:|---|
| Core synthesis examples | `examples/synthesis/*.ae`, `*.aef` | 21 + 3 | Illustrative holes, Z3-tutorial puzzles, and a few classics |
| SMT puzzles | `examples/synthesis/smt/` | 8 | Classic Z3 constraint puzzles (hakank.org/z3) |
| Image-edit predicates | `examples/synthesis/image_edits/` | 6 | Object-selection predicate synthesis over a lattice |
| Micro-benchmarks | `examples/benchmarks/` | 11 | Tiny, focused synthesizer-efficiency probes |
| MBPP | `examples/MBPP/` | 427 | Mostly Basic Python Problems, as refinement specs |
| PSB2 | `examples/PSB2/` | 65 | Program Synthesis Benchmark 2 tasks (incl. `solved/`) |
| Ninety-Nine Problems | `examples/99problems/` | 39 | The classic "99 Lisp/Prolog problems" over lists |
| Property-based testing | `examples/pbt/` | 4 | Synthesis driven by `@assert_property` specs |
| Vericoding | `benchmarks/vericoding/` | 99 tasks | Dafny→Aeon translation harness (generated, not committed) |

The folders swept by CI (`run_examples.sh`) are `ffi`, `image`, `imports`,
`list`, `syntax`, `synthesis`, `synthesis/image_edits`, `PSB2/solved`, and
`99problems`. The remaining suites (MBPP, the full PSB2 tree, Vericoding) are
larger research corpora exercised on demand rather than on every push.

## Core synthesis examples — `examples/synthesis/`

A mixed set of small programs, each with a `?hole` (sometimes guided by a
`@minimize_int` / `@maximize_int` / `@minimize_float` objective).

**Illustrative / language-feature holes:** `int.ae` (synthesize `x == 35`),
`simple_synthesis.ae`, `hole.ae`, `dummy.ae`, `synthesis_proposal.ae`,
`hole_refined_synthesis.ae`, `function_refined_synthesis_args.ae`,
`multiobjective.ae`, and `cputime_energy.ae` (optimizes a hole for
value-correctness *and* CPU time / energy).

**Z3-tutorial puzzles** (ported from public Z3 introductions): `linear_equation.ae`,
`quadratic.ae`, `system_equations.ae`, `circle_points.ae`, `coin.ae`,
`bank_deposit.ae`, `stock_profit.ae`, `page_layout.ae`, `pizza.ae`,
`distinct_triples.ae`.

**Classics:** `nqueens.ae` (N-Queens via inductive types + pattern matching)
and `supermario.ae` (a level generator).

**List synthesis (`.aef`):** `list_Empty.aef`, `list_Insert.aef`,
`list_Replicate.aef` — synthesize list operations against size refinements.

## SMT puzzles — `examples/synthesis/smt/`

Eight classic Z3/SMT constraint puzzles from
[Hakan Kjellerstrand's collection](https://www.hakank.org/z3/), re-expressed as
Aeon synthesis problems (see the suite's own
[README](../examples/synthesis/smt/README.md)): `abbots_puzzle`,
`archery_puzzle`, `bales_of_hay`, `book_buy`, `broken_weights`, `coin_change`,
`mamas_age`, `seseman`. Each bounds its variables with argument refinements,
exposes fields through measure functions, and leaves a `?hole` for the solver.

## Image-edit predicates — `examples/synthesis/image_edits/`

Six object-selection tasks (highlight nuclei, select players, recolor apples,
blur plates, recolor shoes, cut out a team) where the synthesizer learns a
selection predicate from positive/negative examples via a cost objective.

## Micro-benchmarks — `examples/benchmarks/`

Eleven minimal probes for synthesizer behaviour, e.g. integer-interval
constraints (`bench_int_bounded`, `bench_int_negative`, `bench_int_disjoint`,
`bench_int_divisible`), function discovery (`bench_function_clamp`,
`_increment`, `_negate`), and inductive shapes (`bench_list`, `bench_maybe`,
`bench_peano`, `bench_tree`).

## Larger research corpora

* **MBPP** (`examples/MBPP/`, 427 tasks) — "Mostly Basic Python Problems"
  rendered as refinement specifications with a hole.
* **PSB2** (`examples/PSB2/`, 65 `.ae`) — Program Synthesis Benchmark 2 tasks,
  including a curated `solved/` set (run in CI) and `annotations/` with
  single- and multi-objective fitness variants.
* **Ninety-Nine Problems** (`examples/99problems/`, 39 tasks) — the classic
  list-processing problems, used as verification/synthesis exercises.

## Property-based testing — `examples/pbt/`

Four examples that synthesize a function body to satisfy `@assert_property`
specifications (e.g. `synth_int(x)` such that `x + synth_int(x) == 0`).

## Vericoding — `benchmarks/vericoding/`

A harness that translates a subset of the
[Vericoding](https://github.com/Beneficial-AI-Foundation/vericoding-benchmark)
Dafny verification tasks into Aeon synthesis problems and runs them
(issue [#194](https://github.com/alcides/aeon/issues/194)). The `.ae` files are
*generated on demand* by `translate.py` rather than committed. The v1 subset
covers 99 integer/boolean tasks (no sequences, quantifiers, loops, or ghost
code); the committed [REPORT.md](../benchmarks/vericoding/REPORT.md) records a
**59.6% pass rate** (59 pass / 32 fail-synth / 2 fail-parse / 6 rejected) with
the `tdsyn_enumerative` backend. See the suite
[README](../benchmarks/vericoding/README.md) for the translation table and how
to run a sweep.
