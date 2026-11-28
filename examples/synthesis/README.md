# Local synthesis examples

## Reproducible CI synthesis

Use CPython opcode and Z3 resource quotas instead of seconds for deterministic
searches:

```sh
python -m aeon --no-main -s enumerative --seed 0 \
  --opcode-budget 500000 --evaluation-opcode-budget 1000000 --smt-rlimit 100000 \
  examples/synthesis/minimize_size.ae
```

`--opcode-budget` replaces `--budget`. It counts executed opcodes in Aeon's
Python code during each hole search (one shared search for joint holes),
including generation and validation. Worker transport and UI presentation are
excluded, so scheduling and logging speed do not consume search work. Candidate
computations receive separate, fresh `--evaluation-opcode-budget` quotas that
also count foreign Python code (but cannot interrupt a native C/C++ call). Z3
and CVC5 checks use `--smt-rlimit` resource units with their wall-clock timeout disabled.
CP-SAT uses `--cp-sat-work` deterministic solver units (default 1) and one worker.
Search returns a completed incumbent on opcode exhaustion; exhaustion without
an incumbent fails. GP uses a fixed population of 100 instead of timing-based
population sizing. `--seed` controls seeded synthesis as well as PBT.

The backends listed below support this mode, including explicit tactic
scripts and sampled properties. CPU-time/energy objectives remain inherently
machine-dependent and are rejected. This is a shared budget interface, not a claim
that equal quotas give different methods equal computational effort.

| Backend | Deterministic limit and remaining restriction |
| --- | --- |
| `sygus` | CVC5 resources plus a metered solver worker; retains the existing Int/Bool/Float translation subset |
| `boolean_bounded` | Metered CEGIS, Z3 resources, selector/node caps; still requires the supported finite Boolean CNF fragment |
| `polynomial` | Metered certificate construction and Z3 resources; configured degrees and coefficient limits remain |
| `synquid` | Metered enumeration/qualifiers and Z3 resources; the existing refinement/type support is unchanged |
| `ortools` / `ortools_int` / `cpsat` | CP-SAT deterministic work per solve, fixed seed and one worker; requires supported finite, bounded encodings |
| `fta`, `afta`, `cata`, `contata`, `lta` | Opcode quotas, existing grammar/state bounds, and solver quotas where needed; each retains its supported DSL |
| `symetric` / `xfta` | Opcode quota split between construction and repair; requires numeric/vector outputs for its distance metric |
| `arborist` | Opcode, packed-state and interpreter-step limits; retains its scalar DSL |
| `structure_guided` | Opcode and existing skeleton/element limits; retains the supported recursive shapes |
| `regus` | Opcode/state/plan limits and metered observations; requires the ControlProgram/ControlObservation protocol |
| `amaze` | Opcode, candidate/cost and Z3 limits; the offline profile must be fixed |
| `bustle`, `bustle_baseline` | Opcode/value/weight limits; deterministic guided runs use the Python predictor, avoiding NumPy acceleration differences |
| `rl_mcts` | Opcode/node limits and metered guidance calls; loaded models use CPU inference, one native thread and bounded feature/model sizes |
| `decision_tree` | Fixed random state, finite training cells and depth; native fitting is bounded structurally, not by a CPython counter |
| `noisy` | Metered worker generation/validation and separate observation quotas; fixed rounds, proposals, data sizes and seed |
| `tactics`, one-step actions, explicit scripts | Opcode/SMT quotas and existing tactic-step bounds; one-step actions may intentionally leave subgoals |
| `llm`, provider `llm_*` variants | Rejected: request/token quotas cannot guarantee reproducible model-server responses; use recorded candidates for CI |
| `bnsynth` | Rejected: native PyTorch training is outside opcode accounting and depends on hardware |
| `llm_type_constrained` | Rejected: native Transformer kernels are outside opcode accounting and hardware-dependent logits can change token choices |

Example/property preparation gets a separate opcode allowance. Noisy and SyGuS
workers meter search work independently of parent IPC; individual observations
have fresh evaluation allowances. The evaluation allowance also caps training
cells and loaded guidance-model size/features for native learners. These are
structural work bounds, not elapsed-time guarantees. Property corpora use fixed
seeds/counts; their evaluations use opcode quotas, with watchdogs only for hangs.

Reproducibility requires the same CPython, Aeon, solver and dependency versions,
hash seed, input data, and deterministic fitness functions. Opcode counts are
not stable between Python versions or source revisions. Native/foreign work is
not covered by Python opcodes; Z3 has its own resource quota. A worker safety
watchdog aborts the run if a native call hangs rather than treating the candidate
as an ordinary rejection. It cannot make arbitrary Torch, NumPy, foreign or
network computations deterministic.

The `synthesis-examples` CI job pins CPython 3.13.16, installs `uv.lock` including
the OR-Tools and learned-guidance extras, fixes
`PYTHONHASHSEED=0`, and actually synthesizes examples under these quotas. Its
tests require success instead of skipping when a machine is slow. The recursive
example shards continue to check compilation of the full example collection.

This overview covers 112 `.ae` programs and three legacy `.aef` files, excluding
the DP-GP examples being removed in a separate PR. The
`.ae` count includes 99 programs with explicit holes and 13 completed reference/property
examples used alongside synthesis. ARC, Fandango, and RL-MCTS examples live in
[benchmarks/arc/](../benchmarks/arc/), [benchmarks/fandango/](../benchmarks/fandango/),
and [benchmarks/rlmcts/](../benchmarks/rlmcts/).

## Organization

| Directory | `.ae` files | Contents |
| --- | ---: | --- |
| [control/](control/README.md) | 8 | CartPole, pendulum, thermostat, and cruise-control policies, plus the reference runner |
| [puzzle/](puzzle/README.md) | 19 | Constraint, arithmetic, scheduling, and circuit-synthesis problems |
| [leveldesign/](leveldesign/README.md) | 4 | Super Mario levels, dungeons, pizza assignments, and page layouts |
| [lists/](lists/README.md) | 1 | Synthesize a list of length ten; includes a cross-backend runner and measured results |

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
