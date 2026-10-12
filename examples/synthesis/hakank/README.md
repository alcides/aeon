# Hakank common CP models in Aeon

The requested [archived catalogue](https://web.archive.org/web/20251201043639/https://www.hakank.org/common_cp_models/)
contains 1,124 entries. [catalogue.json](catalogue.json) tracks every entry by
its archive anchor, including pinned sources and current porting status.
There are 53 independently validated examples and 892 additional generated
translations in [catalogue/](catalogue/). **The full port is still in progress:**
generated translations have not all been compiled or independently validated,
and 179 entries remain pending. Pending records are inventory, not implementations.

The models use refined scalar holes, Boolean decisions, pure recursive `Vec`
functions, named predicates, and hard `@require` constraints. Aeon searches
all decisions jointly. The authoring importer translates equations; generated
programs do not invoke MiniZinc, FlatZinc, or upstream solvers at runtime.
The catalogue and original formulations are by Hakan Kjellerstrand; the
[upstream MIT license](UPSTREAM_LICENSE) is preserved here.

## Run

Install Aeon's `synthesis-ortools` extra, then run, for example:

```bash
python -m aeon --budget 10 -s ortools examples/synthesis/hakank/send_more_money.ae
python -m aeon --budget 10 -s ortools examples/synthesis/hakank/assignment.ae
python -m aeon --budget 10 -s ortools examples/synthesis/hakank/schedule1.ae
```

Each file imports Aeon's `Vec` library. Integer and Float decisions have
explicit refined domains; Boolean decisions have type `Bool`. `valid` contains
the constraints, while `objective` and `score` state the optimization goal.
`@require(valid)` makes feasibility mandatory, independently of the objective.
Satisfaction problems minimize the constant zero. Knapsack maximization uses
`455 - benefit`. `main` prints the score and decisions.

CP-SAT searches Float holes on its configured fixed-point grid (default 0.001).
Decimal constants retain their precision; the search grid still limits which
real-valued assignments can be represented. An infeasible grid instance does
not establish infeasibility over continuous reals. A timeout may return a
feasible incumbent without proving optimality. These limitations are particularly
relevant to unverified generated translations.

`@require` currently needs the OR-Tools backend. Other backends explicitly
reject it rather than silently replacing hard constraints with a penalty.
Finite set variables are represented by Boolean membership holes, with a
source-element map in the catalogue. Recursive `Vec` operations execute as
Aeon functions and are unfolded structurally during symbolic translation.

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

## Reproduce catalogue translations

The authoring pipeline requires a checkout of the pinned upstream commit and
MiniZinc 2.9.4. All chosen parameters and data files are explicit in
[prepared_instances.json](prepared_instances.json). The compilation step uses
an empty solver library to decompose globals into primitive constraints and
never runs a solver:

```bash
python -m scripts.prepare_hakank_models --upstream /path/to/hakank \
  --minizinc /path/to/minizinc --cache /tmp/hakank-prepared
python -m scripts.import_hakank_flatzinc --cache /tmp/hakank-prepared \
  --results /tmp/hakank-prepared/results.json \
  --catalogue examples/synthesis/hakank/catalogue.json \
  --destination examples/synthesis/hakank/catalogue
```

Unsupported operations and missing domains remain explicit errors in the
catalogue. Models compiled to constant computations need algorithmic Aeon
ports; they are not represented as fake decision problems. The importer tests
check signed division, reification, indexing, finite sets, and fractional
constants by synthesizing witnesses and checking their meaning.

The native ports include a fixed [7,13]-pack purchasing instance, a reduced
4x4 instance of the 17x17 rectangle challenge, the complete DONALD alphametic,
magic hexagon, and EQ20. `scripts/generate_hakank_manual.py` regenerates these
from explicit data; `tests/hakank_manual_test.py` independently checks their
mathematical goals. Euler 1 computes its summation recursively in Aeon and
synthesizes the resulting answer. Large generated models group their refined
holes into balanced `DecisionTree` values; each hole retains its own type and
domain, and constant indices select fields through pure pattern matching.

For Python reference models, the authoring exporter requires CPMpy 1.1.0,
minizinc-python 0.10.0, and NumPy 2.5.4 in the interpreter passed via
`--capture-python`. It captures the first default model with seed 0 before
constructing a solver, exports its constraints, and checks the resulting model
checksum. These dependencies are absent from Aeon runtime. Native ports also
cover reified distinctness, the bowls-and-oranges placement problem, and the
2012 number-theory optimization with exact prime membership.

Alternate encodings reuse shared mathematical specifications where the goals
are equivalent: pairwise and vector N-Queens, scalar-product alphametics, and
MIP magic squares. Sudoku variants preserve their actual upstream clues,
including the 4x4 C# instance and both complete 9x9 datasets. Global examples
use recursive `Vec` predicates; the bit-pattern example searches 48 typed
Boolean holes and preserves 16-bit truncation and arithmetic right shifts.
Fixed global-constraint demonstrations converted to witness searches say so
explicitly in their instance descriptions.
