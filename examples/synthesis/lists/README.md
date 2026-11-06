# A list of exactly ten elements

[`size_ten.ae`](size_ten.ae) asks for any integer list of length ten:

```aeon
open List

def ten : {xs:(List Int) | List.size xs = 10} := ?body;
```

The elements are unconstrained. There are no examples, optimization objectives,
preconstructed solutions, or custom synthesis primitives. The ordinary `List`
library is in scope, including its constructors and helper functions. This is a
local synthesis example, not a benchmark from a paper.

## Reproduce

From the repository root, with the development environment activated:

```bash
python -m aeon --check examples/synthesis/lists/size_ten.ae
AEON_SEED=0 python -m aeon --budget 10 -s tdsyn_backward examples/synthesis/lists/size_ten.ae
PYTHONPATH=. python examples/synthesis/lists/benchmark.py --output /tmp/list-size-ten.json
```

The runner tries each backend sequentially in a fresh process. Defaults are a
10-second synthesis budget, seed 0, and a 30-second outer process limit. The
outer limit includes imports, compilation, synthesis, and execution, and kills
the worker process group if necessary. `--backend` can be repeated to select
backends; `--budget`, `--timeout`, and `--seed` can also be overridden. The runner
exits normally when experiments finish; consult each record's `status` for
synthesis success or failure.

It uses the normal `AeonDriver` synthesis path, then evaluates the resulting
`ten` binding and inspects its actual `List_cons`/`List_nil` chain. A result
counts as a success only if it contains exactly ten integers. This runtime check
is independent of the SMT `List.size` measure. Search limits and grammars are
left at their backend defaults. No learned RL checkpoint is used.

## Recorded results

The full measurements and diagnostics are in [`results.json`](results.json).
The run used master revision `601aa1bb`, Python 3.13.15, and Linux x86-64 on an
AMD Ryzen Threadripper 3960X. The recorded experiment contains one trial per
backend; these results are not statistical success-rate estimates.

| Backend | Synthesis elapsed | Total wall time | Result |
| --- | ---: | ---: | --- |
| `tdsyn_enumerative` | 10.02s | 12.04s | No solution returned |
| `tdsyn_backward` | 10.03s | 12.06s | No solution returned |
| `tdsyn_random` | 10.02s | 12.05s | No solution returned |
| `synquid` | Not returned | 30.02s | Stopped at outer limit |
| `enumerative` | 0.05s | 2.18s | No solution returned |
| `random_search` | Not returned | 30.04s | Stopped at outer limit |
| `gp` | 10.03s | 12.19s | No solution returned |
| `tactics` | 0.16s | 2.17s | **Invalid: empty list (length 0)** |
| `rl_mcts` | 10.17s | 13.57s | No solution returned |
| `fta` | 1.68s | 3.68s | No solution returned |
| `afta` | 1.60s | 3.63s | No solution returned |
| `cata` | 10.12s | 12.16s | No solution returned |
| `lta` | 10.05s | 12.21s | No solution returned |
| `smt` | 16.86s | 18.93s | No solution returned |

No backend returned a valid solution in this experiment. In particular,
`tactics` reported a synthesized `List_nil`, which evaluates to the empty list
(length **0**). It is recorded as **invalid**, not successful. Writing either
`nil` or `nil{Int}` into the source hole is rejected by the ordinary compiler.
This exposes a discrepancy between synthesis candidate validation and source
checking; this example PR does not change the synthesizers.

Some searches finish early, so their outcomes are reported as **no solution
returned**, rather than all being called timeouts. A timeout or exhausted search
does not establish that the specification is unsatisfiable. The type-directed
and native enumeration/random-search backends use a default expansion bound of
5, and RL-MCTS uses 8; these bounds exclude a direct ten-constructor chain.
Library compositions have different shapes, so this observation alone does not
explain every failed run. Synquid and random search reached the separate outer
limit; SMT also overran its nominal synthesis budget before returning.

The specification was checked separately with explicit lists of lengths 0, 9,
10, and 11: only length 10 was accepted. The accepted ten-zero list was also
executed and its constructor chain checked. These controls were not supplied to
any synthesizer.

## Backend selection

The run includes the full type-directed, grammar, genetic, tactic, tree-search,
automata, and SMT constructor-search backends that can attempt datatype-valued
refinement holes. `tdsyn` is an alias of `tdsyn_enumerative`, so it is not run
twice. Individual `backward_*`/`forward_*` actions are single-step tactics and
are excluded.

Other backends need a different problem shape:

| Backend | Why it is excluded from this experiment |
| --- | --- |
| `sygus`, `boolean_bounded`, `polynomial`, `amaze` | Their output domains do not include this inductive `List Int` hole. |
| `ortools` / `cpsat` | Scalar and native-array solving; an inductive list is a different representation. |
| `arborist`, `decision_tree`, `noisy` | Require scalar outputs and/or scalar training data. |
| `contata`, `bustle`, `bustle_baseline` | Require function inputs and usable I/O examples; length alone does not determine the list elements. |
| `structure_guided` | Requires a unary recursive function with structural I/O examples. |
| `symetric` / `xfta` | Requires a suitable metric objective/feature; none is specified here. |
| `regus` | Targets controller programs with rollout specifications. |
| LLM backends | Require an external model/provider; not exercised in this local comparison. |
