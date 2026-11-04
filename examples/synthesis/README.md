# Local synthesis examples

This overview covers 111 `.ae` programs and three legacy `.aef` files, excluding
the DP-GP examples being removed in a separate PR. The
`.ae` count includes 98 programs with explicit holes and 13 completed reference/property
examples used alongside synthesis. ARC, Fandango, and RL-MCTS examples live in
[benchmarks/arc/](../benchmarks/arc/), [benchmarks/fandango/](../benchmarks/fandango/),
and [benchmarks/rlmcts/](../benchmarks/rlmcts/).

## Organization

| Directory | `.ae` files | Contents |
| --- | ---: | --- |
| [control/](control/README.md) | 8 | CartPole, pendulum, thermostat, and cruise-control policies, plus the reference runner |
| [puzzle/](puzzle/README.md) | 19 | Constraint, arithmetic, scheduling, and circuit-synthesis problems |
| [leveldesign/](leveldesign/README.md) | 4 | Super Mario levels, dungeons, pizza assignments, and page layouts |

The top level contains 12 small language/backend examples and the three legacy
`.aef` files. Karel, neuroevolution, and other existing domain/backend directories
retain their own groups.

## Larger standalone examples

The table lists every remaining `.ae` file with at least 25 code lines. Code
lines are nonblank lines whose first non-whitespace character is not `#`; total
lines include comments and blanks. These measure source size, not search
difficulty or benchmark fidelity. Imported libraries and Python helpers are
excluded, so short entry points can still represent substantial tasks.

| Example | Code lines | Total lines | Task |
| --- | ---: | ---: | --- |
| [leveldesign/supermario.ae](leveldesign/supermario.ae) | 128 | 218 | Generate a structured level; optimize coverage/conflicts and cluster spatial features |
| [leveldesign/dungeon.ae](leveldesign/dungeon.ae) | 91 | 141 | Generate rooms, monsters, and loot under coverage/conflict objectives |
| [puzzle/nand_full_adder.ae](puzzle/nand_full_adder.ae) | 77 | 99 | Synthesize a NAND-only adder satisfying its arithmetic contract while minimizing depth |
| [leveldesign/pizza.ae](leveldesign/pizza.ae) | 71 | 99 | Assign seven distinct pizzas subject to individual preferences |
| [control/pendulum_structure.ae](control/pendulum_structure.ae) | 58 | 68 | Synthesize controller structure with rollout loss and a size penalty |
| [leveldesign/page_layout.ae](leveldesign/page_layout.ae) | 45 | 73 | Place three non-overlapping rectangles within a page |
| [puzzle/magic_square.ae](puzzle/magic_square.ae) | 44 | 66 | Fill a 3×3 magic square |
| [control/thermostat_structure.ae](control/thermostat_structure.ae) | 44 | 52 | Synthesize thermostat controller structure |
| [puzzle/nqueens.ae](puzzle/nqueens.ae) | 42 | 54 | Find a valid queens arrangement |
| [puzzle/nurse_scheduling.ae](puzzle/nurse_scheduling.ae) | 39 | 89 | Satisfy staffing constraints and maximize granted shift requests |
| [puzzle/distinct_triples.ae](puzzle/distinct_triples.ae) | 39 | 56 | Find disjoint triples with equal sums and products |
| [neuroevolution/mnist.ae](neuroevolution/mnist.ae) | 33 | 72 | Optimize neural-network architecture for classification error and hidden-unit count |
| [puzzle/map_coloring.ae](puzzle/map_coloring.ae) | 29 | 52 | Assign colors under adjacency constraints |
| [puzzle/coin.ae](puzzle/coin.ae) | 27 | 45 | Solve a constrained coin-change instance |
| [puzzle/cryptarithmetic.ae](puzzle/cryptarithmetic.ae) | 26 | 42 | Solve TWO + TWO = FOUR with distinct digits |
| [puzzle/stock_profit.ae](puzzle/stock_profit.ae) | 26 | 41 | Choose buy/sell positions maximizing profit |

## Sources and related groups

Source attributions below come from the program headers and existing suite
documentation. They describe provenance separately from the domain folders above.

| Group | Files | Scope and provenance |
| --- | ---: | --- |
| [Level design and assignments](leveldesign/README.md) | 4 | `supermario.ae`, `dungeon.ae`: local structured-generation tasks; `pizza.ae`: a gist puzzle; `page_layout.ae`: a Z3 tutorial port |
| [Control policies](control/README.md) | 8 | Seven synthesis programs and one reference runner; CartPole, pendulum, thermostat, and cruise control. Dynamics, rollouts, and controller DSLs live in `aeon/libraries/Control*.ae`. These use local evaluation protocols. |
| [Karel](karel/README.md) | 21 | Ten synthesis/reference pairs plus one DSL demonstration. The checked-in worlds are local regression fixtures; published-dataset import support is documented separately. |
| [MNIST neuroevolution](neuroevolution/mnist.ae) | 1 | A topology-search task with its own Python fitness helper and fixed dataset subset; a local protocol using a named dataset |
| Gentle introduction to Z3 | 6 | `puzzle/{linear_equation,quadratic,circle_points,coin,system_equations}.ae` and `leveldesign/page_layout.ae`: tutorial ports |
| Hillel Wayne Z3 examples | 3 | `puzzle/{bank_deposit,distinct_triples,stock_profit}.ae`: blog examples |
| pganalyze CP-SAT examples | 3 | `puzzle/{candy_contribution,map_coloring,shift_assignment}.ae`: blog-inspired constraint problems |
| OR-Tools scheduling | 1 | `puzzle/nurse_scheduling.ae`: a downscaled official scheduling example |
| Classic constraint problems | 5 | `puzzle/{cryptarithmetic,knapsack,magic_square,nqueens,scheduling}.ae`: locally encoded instances |
| Other arithmetic/circuit puzzles | 2 | `puzzle/pell_equation.ae`: an equation problem; `puzzle/nand_full_adder.ae`: a constraint-solving article adaptation |
| [Monotonicity](monotonicity/README.md) | 5 | Local function-synthesis tasks with relational refinement proofs |

The seven [OR-Tools backend demos](ortools/) also include small Booth and sphere
objective functions. The [Arborist list-sum variant](arborist/list_sum.ae) adds
local examples to the paper's fold specification. AFTA, CATA, and FTA demos cite
their algorithms' papers; this attribution alone does not establish that the
individual tasks came from the papers' benchmark corpora.

See [ORGANIZATION.md](../ORGANIZATION.md) for the complete remaining inventory
and the [benchmark index](../benchmarks/README.md) for the relocated collections.
