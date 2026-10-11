# Hakank common CP models in Aeon

This starter suite implements **25 representative models**, not all 1,124
entries in the [requested archived catalogue](https://web.archive.org/web/20251201043639/https://www.hakank.org/common_cp_models/).
It covers finite puzzles, global constraints, assignment, packing, scheduling,
and optimization. The catalogue and model formulations are by Hakan
Kjellerstrand. These are new Aeon formulations; no upstream solver runs at
runtime and no solution assignments are embedded in the examples.

## Run

Install Aeon's `synthesis-ortools` extra, then run, for example:

```bash
python -m aeon --budget 10 -s ortools examples/synthesis/hakank/send_more_money.ae
python -m aeon --budget 10 -s ortools examples/synthesis/hakank/assignment.ae
python -m aeon --budget 10 -s ortools examples/synthesis/hakank/schedule1.ae
```

Each file is standalone. Every decision is an integer hole with an explicit
finite domain. `valid` contains the complete constraints, `objective` states
the feasible score, and `score` returns the objective for valid assignments or
1,000,000 otherwise. `@minimize_int(score)` makes Aeon search all decisions
jointly. A satisfaction problem succeeds at score 0; optimization problems
use the target in the table below. Knapsack maximization is expressed as
`455 - benefit`, so all objectives are minimized consistently.

All feasible objective values are nonnegative and strictly below the invalid
penalty. Thus a proven optimum is feasible when a feasible assignment exists.
This is an exact bounded penalty formulation, not a claim that a feasible
solution exists for arbitrary changed instances. A timeout or score 1,000,000
is not a solved benchmark. The backend may return a feasible incumbent before
proving optimality if the budget expires. The tests require the documented
optimal scores, not merely that synthesis returned an expression.

`main` prints the score and every decision. The synthesis output also exposes
the completed definitions. The files include no `native`, FFI, external data,
or reference solutions. Constructor/value grammar search is not required:
CP-SAT translates the arithmetic, comparisons, Boolean combinations, and
numeric conditionals in these models. The added Boolean translation concerns
intermediate expressions; Boolean-valued holes remain unsupported.

## Instances and goals

Sizes and data are fixed for reproducibility. Reduced instances are explicitly
identified; parameterized upstream models are instantiated rather than ported
as general-purpose Aeon solvers. Satisfaction models return one witness, not
all upstream solutions. In particular, Sudoku is a new 4x4 test instance,
all-interval has size 5, Langford has k=3, Golomb has four marks, and bin packing
uses the small [4,3,1] instance listed in the upstream source. Langford uses the
positions of the two copies, an equivalent representation without dynamic
array indexing. Cumulative scheduling checks resource use at every task start: positive
resource use can increase only at a start event. Intervals are half-open.
The independent test additionally checks every occupied integer time slot.

| Model | Instance | Target score |
| --- | --- | --- |
| [all_different_except_0](all_different_except_0.ae) | five values in 0..5; repeated zeros allowed | 0 |
| [all_interval](all_interval.ae) | series of size 5 (reduced instance) | 0 |
| [among](among.ae) | exactly three of five values belong to {1,5,8} | 0 |
| [assignment](assignment.ae) | 4 people, 5 choices (upstream data) | 11 |
| [bin_packing](bin_packing.ae) | weights [4,3,1], capacity 4 (small upstream example) | 2 |
| [discrete_tomography](discrete_tomography.ae) | 11x12 binary image with upstream default row/column sums | 0 |
| [golomb_ruler](golomb_ruler.ae) | four ordered marks, upper bound 10 (reduced instance) | 6 |
| [knapsack](knapsack.ae) | 11 binary items, capacity 102 (upstream data) | 77 |
| [langford](langford.ae) | k=3, positions of two copies (reduced instance) | 0 |
| [magic_sequence](magic_sequence.ae) | length 5 (one of upstream's sizes 1..19) | 0 |
| [magic_square](magic_square.ae) | normal 3x3 square, line sum 15 | 0 |
| [map_coloring](map_coloring.ae) | Belgium/Denmark/France/Germany/Netherlands/Luxembourg, four colors | 0 |
| [nqueens](nqueens.ae) | 8 queens, one per column | 0 |
| [nvalue](nvalue.ae) | five values in 1..5, synthesize their distinct-value count | 0 |
| [quasigroup_completion](quasigroup_completion.ae) | 5x5 completion (upstream default) | 0 |
| [rabbits](rabbits.ae) | nine rabbits/pheasants with 24 legs (upstream data) | 0 |
| [schedule1](schedule1.ae) | seven cumulative tasks, capacity 13, integer starts 1..30 (upstream data) | 23 |
| [send_more_money](send_more_money.ae) | base 10, eight distinct digits | 0 |
| [seseman](seseman.ae) | 3x3 border, each side sums to 9 (upstream default) | 0 |
| [set_covering](set_covering.ae) | six fire-station cities; maximum distance 15 | 2 |
| [ski_assignment](ski_assignment.ae) | 5 people, 6 choices (upstream data) | 7 |
| [subset_sum](subset_sum.ae) | nonnegative counts, total 100 (upstream data) | 0 |
| [sudoku](sudoku.ae) | 4x4 completion (reduced Sudoku instance) | 0 |
| [traffic_lights](traffic_lights.ae) | CSPLib 016, four vehicle/pedestrian pairs | 0 |
| [xkcd](xkcd.ae) | nonnegative counts, total 1505 (upstream data) | 0 |

## Provenance and verification

[manifest.json](manifest.json) records the exact requested archive URL, the
retrieved HTML's SHA-256, each catalogue anchor, fixed instance data, variable
domains, goals, and expected scores. Source links are pinned to upstream
commit `2823c48d3d2e5d86acb3b8e6951172499c8946b0` (2025-11-27), preceding the
archive date. Each referenced upstream file also has a SHA-256. Neither
retrieving sources nor accessing the archive is needed to run these examples.

Regenerate the committed Aeon files from their explicit finite models with:

```bash
python scripts/generate_hakank_examples.py
```

The generator writes model constraints and holes, never solves them. It uses
balanced expression trees and named `Bool` constraints to keep Aeon
compilation practical. The manifest is the provenance input; generator-owned
instance fields are refreshed deterministically.

Run verification using only the test and solver extras:

```bash
uv run --extra tests --extra synthesis-ortools pytest \
  tests/hakank_cp_examples_test.py tests/ortools_cpsat_test.py -q
```

Tests compile and synthesize every instance, check scalar domains, independently
validate the combinatorial assignment in Python, and evaluate the completed
Aeon score. Assignment/ski matching and knapsack optima are additionally checked
by exhaustive enumeration over independent representations. Scheduling attains
the resource-area lower bound, establishing optimality independently. A generation test
checks that committed examples match the generator and manifest. The optional
OR-Tools CI job runs this suite; core-only installations skip solver tests.
