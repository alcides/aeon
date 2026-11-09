# 50-item knapsack solver comparison

Initial run on 2026-11-09 at `b3e7eae74ebfcf2db393377aff64e5839a6dfc72`,
after merging #680 and #684. The example is unchanged:
[`knapsack_50.ae`](https://github.com/alcides/aeon/blob/master/examples/synthesis/puzzle/knapsack_50.ae) returns a
50-node Boolean `Mask`, with count and weight tracked logically. Capacity is
100 and `@maximize` scores the selected values.

## Method

Each backend ran in a fresh process on Linux x86-64, Python 3.13.15, with
`AEON_SEED=0` and `PYTHONHASHSEED=0`. The synthesis budget was 60 seconds and
the process watchdog was 180 seconds. Runs were sequential.

For each successful synthesis, the returned program was evaluated and its
result independently checked: exactly 50 Boolean nodes, total weight at most
100, and total value recomputed from the data arrays. A separate 0/1 dynamic
program over those arrays establishes that the optimal value is **1077**.

The times below include parsing, synthesis, and evaluation, but exclude Python
imports. Parsing took about seven seconds. These are individual runs, not a
before/after speedup measurement. Search budgets do not currently interrupt an
in-progress whole-program validation; both successful TDSyn runs overran the
60-second budget.

| Backend | Outcome | Total seconds | Weight | Value |
| --- | --- | ---: | ---: | ---: |
| `ortools` (CP-SAT) | Optimal solution | 40.5 | 100 | 1077 |
| `tdsyn_backward` | Feasible solution | 159.1 | 68 | 291 |
| `tdsyn_enumerative` | Feasible solution | 148.7 | 99 | 406 |
| `tdsyn_random` | No solution within budget | 67.0 | — | — |
| `gp` | Missing SMT function assertion | 54.2 | — | — |
| `random_search` | No solution within budget | 68.5 | — | — |
| `enumerative` | No solution within budget | 67.2 | — | — |
| `synquid` | Unresolved datatype predicate error | 13.4 | — | — |
| `rl_mcts` | No solution; one complete candidate checked | 67.1 | — | — |
| `noisy` | Unsupported goal | 7.0 | — | — |

Synthesis itself took 33.4 seconds for CP-SAT, 152.1 seconds for
TDSyn-backward, and 141.6 seconds for TDSyn-enumerative. The latter two results
are feasible, not optimal.

GP raised `AssertionError: Function fits… not found in SMT context` during
whole-program validation. Synquid raised `ValueError: Unresolved datatype
predicate` while materializing a match handler's predicate. Noisy requires
scalar literal input/output equalities and cannot accept this optimization
goal.

Both crashes were reproduced with the same runner, seeds, and limits on the
merged master (`1e032a14cce6d04fe9c0c13d42c28ecbf5e8cc34`), before these two
optimizations: GP failed with the identical missing `fits` function assertion
after 54.4 seconds and Synquid with the identical predicate error after 13.2
seconds. These failures preceded the performance changes. The follow-up below
fixes their generation paths.

The constructor-sharing change reduces repeated proof expansion when a
backend reaches validation. It does not change the backend's grammar, depth
limits, or search strategy. Incremental Synquid queries reuse validity
obligations, but do not provide a specialized generator for a 50-node mask.
These optimizations therefore do not make every backend solve this example.

## GP and Synquid generation fixes

A second run on the same day, with the same example, seeds, limits, and
independent result checks, produced valid masks from both backends:

| Backend | First valid candidate, seconds | Synthesis seconds | Total seconds | Weight | Value |
| --- | ---: | ---: | ---: | ---: | ---: |
| `gp` | 32.5 | 62.3 | 69.3 | 99 | 538 |
| `synquid` | 32.3 | 61.5 | 68.4 | 100 | 459 |

Both results contain exactly 50 Booleans. They are feasible, not optimal; the
optimum remains 1077. Final validation still slightly overruns the search
budget. The changes address three generation problems:

- GP's component library admitted SMT-only projections, including
  `Mask_cons_used`. These are logical functions without executable values and
  now stay out of the grammar while still shadowing older bindings.
- Synquid replaced solved abstract predicates with unrelated implicit holes.
  It now retains goal relations and emits the predicate assignment it solved,
  with operator instantiations elaborated for Core checking. A match requiring
  an unresolved predicate is skipped rather than crashing the entire search.
- Both solvers searched for the list spine even though the type fixes its
  length. They now share the existing CP-SAT constructor-schema analysis to
  unroll fixed-size Boolean lists. GP evolves each Boolean preference, with
  feasibility checks repairing invalid choices. Synquid enumerates feasible
  assignments. Neither delegates its objective search to CP-SAT.

Field refinements, tail preconditions, and the final result predicate all
remain in the generation constraints. Unknown SMT answers produce no model,
and every proposed term still passes normal validation before acceptance.

## Reproduce

From the checkout being measured, with the development and optional OR-Tools
and RL-MCTS dependencies installed:

```bash
python scripts/bench_knapsack_solvers.py \
  --budget 60 --wall-limit 180 --output /tmp/knapsack-results
```

Use `--backends gp synquid`, for example, to select a subset. The runner saves
per-backend logs, JSON results, successful Boolean decisions, and an aggregate
`results.json`. A timed-out process is terminated, and stale output from an
earlier invocation is cleared before each backend starts. To compare an older
checkout, run this script by its absolute path with that checkout as the
working directory.
