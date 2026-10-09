# Program synthesis benchmarks

Aeon ships with a large collection of programs that exercise hole filling
(`?hole`) under liquid types and fitness objectives. They double as a
regression suite (a subset runs in CI via `run_examples.sh`) and as a catalogue
of what liquid-type-guided synthesis can express.

For the synthesizer backends these benchmarks target (`gp`, `enumerative`,
`tdsyn`, `synquid`, `afta`, `symetric`, …), see [synthesizers.md](synthesizers.md).

## How to run

```bash
# Synthesize a hole (genetic programming, 30s budget):
uv run python -m aeon --budget 30 -s gp examples/synthesis/nqueens.ae

# Type-check only, without synthesis (fast parser/elaboration check):
uv run python -m aeon -n examples/synthesis/smt/abbots_puzzle.ae

# CI example suite (non-recursive; exit 2 = no solution within budget is OK):
bash run_examples.sh
```

**Global defaults.** `--budget` defaults to **60s**. CI via `run_examples.sh`
uses **`--budget 10`**. Recommended timeouts below come from suite READMEs,
file headers, or tests when available; otherwise a suggested default for the
problem class is given.

---

## Suites at a glance

| Suite | Location | Count | Origin | Recommended timeout |
|---|---|--:|---|---|
| Core / mixed top-level | `examples/synthesis/*.ae`, `*.aef` | 51 + 3 | Mixed (see below) | CI **10s**; many files **30–60s** |
| SMT puzzles | `examples/synthesis/smt/` | 8 | hakank.org/z3 | **60s** (`gp`) |
| Image-edit predicates | `examples/synthesis/image_edits/` | 6 | arXiv:2504.03155-inspired | **30–60s** (`gp`) |
| Inverse CSG | `examples/synthesis/csg/` | 47 | SyMetric / Feser et al. | **60–300s** (`symetric`/`gp`); CI smoke **8s** |
| Synquid | `examples/synthesis/synquid/` | 64 | Synquid PLDI’16 | **30s** (`synquid`/`gp`) |
| SRBench (Feynman + Strogatz) | `examples/synthesis/srbench/` | 134 | SRBench / AI Feynman / ODE-Strogatz | **60s** (`gp`) |
| AFTA SyGuS PBE-Strings | `examples/synthesis/afta/sygus/` | 109 | SyGuS PBE_SLIA / BLAZE POPL’18 | **60s** (`afta`) |
| Absynthe SyGuS strings | `examples/synthesis/absynthe/` | 7 | Absynthe Rust artifact | evaluator / exact-target fitness |
| AFTA matrix | `examples/synthesis/afta/matrix/` | 10 | BLAZE Fig.17 reconstruction | **60s** (`afta`) |
| AFTA demos | `examples/synthesis/afta/*.ae` | 2 | Wang et al. POPL’18 | **10–15s** (`afta`) |
| CATA demos | `examples/synthesis/cata/*.ae` | ~10 | Contata / CAV spirit | **30s** (`cata`) |
| Contata transcription | `examples/synthesis/cata/contata/` | 30 | Contata artifact | **30–60s** when attempting synth; often `--test` |
| DACE + FTA | `examples/synthesis/dace/`, `fta/` | 16 + 3 | DACE OOPSLA’17 | FTA synth **10s**; PBE **60s** |
| OR-Tools IntHole | `examples/synthesis/ortools/` | 7 | Aeon-native CP-SAT | **5–8s** (`ortools`) |
| AutoNumerics | `examples/synthesis/autonumerics/` | 3 | AutoNumerics-Zero / HUMIES’26 | **30–120s** |
| Grover circuits | `examples/synthesis/grover/` | 1 | GECCO’26 HUMIES Bronze | **30s** (`gp`) |
| Neuroevolution MNIST | `examples/synthesis/neuroevolution/` | 1 | Aeon-native NN | **60s** (`random_search`) |
| Micro-benchmarks | `examples/benchmarks/` | 11 | Aeon-native probes | **5–15s** |
| PSB2 | `examples/PSB2/` | 65 | Program Synthesis Benchmark 2 | CI **10s** on `solved/`; research **60s+** |
| MBPP | `examples/MBPP/` | 427 | Mostly Basic Python Problems | **30–60s** |
| 99 problems | `examples/99problems/` | 39 | Classic list problems | CI **10s** |
| PBT | `examples/pbt/` | ~11 | Aeon `@assert_property` / `@example` | **10–30s** for synth-oriented files |
| Vericoding | `benchmarks/vericoding/` | 99 (generated) | Dafny Vericoding → Aeon | harness **30s**; sweep **60s** |

CI (`run_examples.sh`) sweeps only: `ffi`, `image`, `imports`, `list`, `mutual`,
`syntax`, `synthesis` (non-recursive), `synthesis/image_edits`, `verification`,
`PSB2/solved`, `99problems`. Large research corpora (SRBench, Synquid, CSG,
SyGuS, MBPP, full PSB2, Vericoding) are on-demand.

---

## Core top-level — `examples/synthesis/`

Mixed small programs with a `?hole`, often guided by `@minimize_*` /
`@maximize_*` / `@property`. Subdirectories are **not** swept by CI.

| Family | Paths | Origin | Description | Timeout |
|---|---|---|---|---|
| Language / hole demos | `int.ae`, `hole.ae`, `dummy.ae`, `simple_synthesis.ae`, `synthesis_proposal.ae`, `hole_refined_synthesis.ae`, `function_refined_synthesis_args.ae`, `multiobjective.ae`, `cputime_energy.ae` | Aeon-native | Refined ints, args, multi-obj, cputime/energy | **10–30s** |
| Z3 tutorial ports | `linear_equation.ae`, `quadratic.ae`, `circle_points.ae`, `coin.ae`, `page_layout.ae`, `system_equations.ae` | [Gentle introduction to Z3](https://ar-ms.me/thoughts/a-gentle-introduction-to-z3/) | Integers / points / coins / layout under refinements | **10–30s** |
| Hillel Wayne Z3 | `bank_deposit.ae`, `distinct_triples.ae`, `stock_profit.ae` | [Hillel Wayne Z3 examples](https://www.hillelwayne.com/post/z3-examples/) | Deposit, triples, buy/sell indices | **15–60s** |
| Pizza | `pizza.ae` | External gist (pizza prefs) | Assignment under preferences | **30s** |
| Classic Boolean GP | `even_parity.ae`, `multiplexer.ae` | Koza (1992) | Even-3-parity / 6-mux | **30s** / **60s** (file headers) |
| Classic SR | `koza_quartic.ae`, `pagie1.ae` | Koza (1992); Pagie & Hogeweg (1997) | Rediscover \(x^4+\cdots+x\); Pagie-1 | **30s** / **60s** (file headers) |
| ARC Prize 2024 | `arc_*.ae` (7) | ARC Prize 2024 / Kaggle ARC | 3×3 grid transforms (mirror, rotate, recolor, gravity, …) | **30–60s** |
| Constraint fuzzing | `fuzzing_*.ae` (9) | Inspired by Fandango | Valid IPv4, ISBN, ISO8601, dates, RGB, triangle, … | **15–60s** |
| CP / scheduling | `candy_contribution.ae`, `cryptarithmetic.ae`, `knapsack.ae`, `magic_square.ae`, `map_coloring.ae`, `nurse_scheduling.ae`, `scheduling.ae`, `shift_assignment.ae` | CP-SAT / OR-Tools tutorials | Satisfying or soft-optimized assignments | **30–60s** (`ortools` where applicable) |
| PCG | `supermario.ae`, `dungeon.ae` | Aeon-native (`@cluster` on Mario) | Level / dungeon under multi-obj | **60s+** (`symetric`/`gp`) |
| List `.aef` | `list_Empty.aef`, `list_Insert.aef`, `list_Replicate.aef` | Aeon-native | List ops vs size refinements | **30s** |
| Other | `nqueens.ae`, `pell_equation.ae` | Aeon / math | 9-queens board; Pell solver + `@property` | **30–60s** |

```bash
uv run python -m aeon --budget 30 -s gp examples/synthesis/nqueens.ae
uv run python -m aeon --budget 30 -s gp examples/synthesis/even_parity.ae
uv run python -m aeon --budget 60 -s gp examples/synthesis/pagie1.ae
```

---

## SMT puzzles — `examples/synthesis/smt/` (8)

**Origin.** [Hakan Kjellerstrand’s Z3 collection](https://www.hakank.org/z3/)
(issue [#130](https://github.com/alcides/aeon/issues/130)).

**Description.** Inductive `mk …` constructors with argument refinements;
measure fields; a refined `?hole` for the puzzle solution.

| File | Puzzle |
|---|---|
| `abbots_puzzle.ae` | Dudeney, Abbot’s Puzzle |
| `archery_puzzle.ae` | Sam Loyd archery |
| `bales_of_hay.ae` | Pairwise hay-bale weights |
| `book_buy.ae` | Kraitchik Book Buy |
| `broken_weights.ae` | Bachet broken weight |
| `coin_change.ae` | Min coins to 37 |
| `mamas_age.ae` | Dudeney Mamma’s Age |
| `seseman.ae` | Seseman convent |

**Timeout.** README: **`--budget 60 -s gp`**.

---

## Image-edit predicates — `examples/synthesis/image_edits/` (6)

**Origin.** Inspired by *Synthesizing Optimal Object Selection Predicates for
Image Editing using Lattices* ([arXiv:2504.03155](https://arxiv.org/abs/2504.03155)).

**Description.** Learn a Boolean selection predicate from ± examples under a
cost objective (`cell_microscopy`, `football_players`, `green_apples`,
`license_plates`, `shoe_recolor`, `team_jerseys`).

**Timeout.** Not file-specified; CI **10s**. Suggested research: **30–60s** `gp`.

---

## Inverse CSG — `examples/synthesis/csg/` (47)

**Origin.** Feser, Dillig & Solar-Lezama, *Metric Program Synthesis for Inverse
CSG* ([arXiv:2206.06164](https://arxiv.org/abs/2206.06164)); SyMetric artifact
(`github.com/jfeser/symetric`).

**Description.** Recover a CSG AST (`Circle` / `Rect` / `Union` / `Diff` /
`Repeat`) matching a 32×32 target via `@minimize_float(jaccard …)` and
`@cluster(scene …)` for `-s symetric`. Rasterisation lives in `csg_metric.py`
(Pillow). Sizes: tiny (2), small (13), medium (6), large (1), generated (25).

**Timeout.**

| Source | Value |
|---|---|
| This docs page / typical research run | **60s+** `gp` / `symetric` |
| `tests/symetric_test.py` | **8s** CLI smoke on `csg_tiny_two_circle.ae` |
| Full suite | Often **60–300s** by size; out of CI |

```bash
uv run python -m aeon --budget 60 -s symetric examples/synthesis/csg/csg_tiny_two_circle.ae
```

---

## Synquid — `examples/synthesis/synquid/` (64)

**Origin.** Polikarpova, Kuraj & Solar-Lezama, *Program Synthesis from
Polymorphic Refinement Types* (PLDI 2016); ports of Synquid `test/pldi16`.

**Description.** Refinement-typed list / tree / BST / heap / AVL / RBT /
AddressBook / Evaluator APIs. By family: List (30), IncList (3), StrictIncList
(3), Tree (4), BST (4), BinHeap (5), AVL (6), RBT (3), AddressBook (2),
Evaluator (1), UniqueList (3). See the suite
[README](../examples/synthesis/synquid/README.md) for fidelity tiers.

**Timeout.** README: **`--budget 30 -s synquid`** (or `gp`). A handful solve at
**~3s**. Not in CI.

```bash
uv run python -m aeon --budget 30 -s synquid examples/synthesis/synquid/List-Reverse.ae
```

---

## SRBench — `examples/synthesis/srbench/` (134)

**Origin.** [SRBench](https://cavalab.org/srbench/) ground-truth half (La Cava
et al., 2021): Feynman Symbolic Regression Database (Udrescu & Tegmark) and
[ODE-Strogatz](https://github.com/lacava/ode-strogatz).

**Description.** Rediscover a known Float equation; fitness = MAE over 30
samples (`feynman_*.ae` × 120, `strogatz_*.ae` × 14). Black-box SRBench
datasets are omitted (no closed form).

**Timeout.** README: **`--budget 60 -s gp`**. Not in CI (too many / too long for
10s).

```bash
uv run python -m aeon --budget 60 -s gp examples/synthesis/srbench/feynman_i_6_20.ae
```

---

## AFTA / BLAZE / SyGuS — `examples/synthesis/afta/`

### Demos (2)

| Path | Origin | Description | Timeout |
|---|---|---|---|
| `abstraction_refinement.ae` | Wang, Dillig & Singh POPL’18 ([arXiv:1710.07740](https://arxiv.org/abs/1710.07740)) | CEGAR AFTA on multi-conjunct Int refinement | **10s** CLI / **15s** API (`tests/afta_test.py`) |
| `pbe_firstname.ae` | BLAZE-style string PBE | Extract first 3 chars via `@example` | **15–40s** in PBE tests; suite default **60s** |

### SyGuS PBE-Strings — `afta/sygus/` (109)

**Origin.** SyGuS PBE-Strings / BLAZE evaluation suite; converted by
`scripts/sygus_to_aeon.py` from SyGuS-Org `PBE_SLIA_Track`.

**Description.** String transformers from `@example` I/O. Coverage still WIP
(missing some String DSL ops / grammar scoping).

**Timeout.** README: **`--budget 60 -s afta`**.

### Absynthe SyGuS strings — `examples/synthesis/absynthe/` (7)

**Origin.** The [Absynthe Rust artifact](https://github.com/ngsankha/absynthe-rust),
commit `54613a6` (issue [#561](https://github.com/alcides/aeon/issues/561)).

**Description.** A representative, executable SLIA SyGuS corpus covering
`bikes`, `phone`, and name-formatting transformations.  The files are read by
`aeon.synthesis.benchmarks.absynthe`, a typed interpreter for the artifact's
String/Int/Bool grammar.  Its fitness is the number of violated constraints;
fitness `0` denotes an exact target.  These are backend-neutral data fixtures,
not `.ae` source programs.

### Matrix domain — `afta/matrix/` (10)

**Origin.** BLAZE matrix DSL (Fig.17) reconstruction (paper’s 39 forum tasks
were not published individually).

**Description.** Matrix string transforms (`reshape`, `transpose`, flips,
compositions).

**Timeout.** README: **60s** `afta`.

---

## CATA / Contata — `examples/synthesis/cata/`

**Origin.** Miltner, Wang, Chaudhuri & Dillig, Contata (relational / constraint-
annotated tree automata synthesis).

### Demo holes (~10 top-level `.ae`)

Examples such as `double`, `square`, `pred`, `neg`, `conditional_select`,
`operator_relational`, `mutual_cosynth`, `mutual_pbe`, `contata_pbe`,
`relational_property`.

**Timeout.** README: **`--budget 30 -s cata`**; `tests/cata_test.py` CLI **30s**.

### Full Contata transcription — `cata/contata/` (30)

**Origin.** Contata artifact (`github.com/amiltner/ContataArtifactEvaluation`),
30 `.mls` → Aeon (`mutrec/` 7, `reccomp/` 7, `ds/` 12, `stackoverflow/` 4).

**Description.** Mostly checked reference + `@property` / `@example` specs;
not all solvable by the current Contata Int/Bool/`List Int` domain.

**Timeout.** Prefer `aeon --test` for verification; when synthesizing,
**30–60s** `contata` / `cata` on flagships.

---

## DACE + FTA — `examples/synthesis/dace/`, `fta/`

**Origin.** Wang, Dillig & Singh, *Synthesis of Data Completion Scripts using
Finite Tree Automata* (OOPSLA 2017; [arXiv:1707.01469](https://arxiv.org/abs/1707.01469)).

| Subset | Count | Role | Timeout |
|---|--:|---|---|
| Top-level pipelines | 8 | Execute DACE DSL (not synth) | N/A |
| `dace/synth/` | 3 | Cell completion via `-s fta` | **10s** |
| `dace/pbe/` | 5 | Sec.2 PBE examples | **60s** |
| `fta/*.ae` | 3 | Standalone FTA demos | File **10s**; tests **15–25s** |

```bash
uv run python -m aeon --no-main -s fta --budget 10 examples/synthesis/dace/synth/<file>.ae
```

---

## OR-Tools IntHole — `examples/synthesis/ortools/` (7)

**Origin.** Aeon-native CP-SAT hole optimisation.

**Files.** `int_sphere`, `int_booth`, `int_constrained`, `int_let`,
`float_quadratic`, `array_int`, `array_float`.

**Timeout.** `scripts/bench_ortools.py` uses **`BUDGET = 5`**;
`tests/ortools_cpsat_test.py` helper **8s**.

```bash
uv run python scripts/bench_ortools.py
```

---

## AutoNumerics-Zero — `examples/synthesis/autonumerics/` (3)

**Origin.** Real et al., AutoNumerics-Zero (ICML 2026;
[arXiv:2312.08472](https://arxiv.org/abs/2312.08472); HUMIES 2026 Gold).

| File | Role | Timeout |
|---|---|---|
| `exp2_pade.ae` | Coefficient search on fixed \(a^2/(1+bx)+c\) skeleton | **30s** `ortools` (header suggests **30–120s**) |
| `exp2_free.ae` | Free-form \(2^x\) approximation | **30s** for demos |
| `exp2_reference.ae` | Paper programs f2…f10 as reference | Verification / comparison |

---

## Grover circuits — `examples/synthesis/grover/` (1)

**Origin.** Obidiegwu et al., evolving hardware-efficient Grover circuits
(GECCO 2026; HUMIES Bronze).

**Description.** Post-Hadamard 3-qubit gate sequence maximizing \(P_{target}\)
vs gate count (`grover_circuits.ae`).

**Timeout.** File header: **`--budget 30 -s gp`**.

---

## Neuroevolution — `examples/synthesis/neuroevolution/` (1)

**Origin.** Aeon-native multi-objective MLP topology search on an MNIST subset
(requires `.[nn]`).

**Description.** Synthesize `Arch` (hidden widths/activations); fitness
`[error, n_hidden]` via `@multi_minimize_*`.

**Timeout.** File header: **`--budget 60 -s random_search`**.

---

## Micro-benchmarks — `examples/benchmarks/` (11)

**Origin.** Aeon-native synthesizer-efficiency probes.

**Description.** Tiny refined ints (`bench_int_bounded`, `_negative`,
`_disjoint`, `_divisible`), function discovery (`bench_function_clamp`,
`_increment`, `_negate`), inductive shapes (`bench_list`, `bench_maybe`,
`bench_peano`, `bench_tree`).

**Timeout.** Not specified → **5–15s** (`enumerative` / `synquid` / `smt` /
`tdsyn`). Not in CI.

---

## Larger research corpora (outside `examples/synthesis/`)

### PSB2 — `examples/PSB2/` (65)

**Origin.** Program Synthesis Benchmark 2.

**Layout.** Root tasks + `solved/` (**25**, CI) + `annotations/` (single/multi-
objective variants).

**Timeout.** CI **10s** on `solved/`; research runs typically **60s+**.

### MBPP — `examples/MBPP/` (427)

**Origin.** Mostly Basic Python Problems as fitness + hole.

**Timeout.** Not specified → **30–60s** `gp`. Parse-only tests use budget **0**.

### Ninety-Nine Problems — `examples/99problems/` (39)

**Origin.** Classic 99 Lisp/Prolog list problems (often verification-first).

**Timeout.** CI **10s**.

### PBT — `examples/pbt/` (~11)

**Origin.** Aeon `@assert_property` / `@example` synthesis and testing.

**Timeout.** CI runs many with `--test` (no synth budget). Synth-oriented files
→ **10–30s**.

### Vericoding — `benchmarks/vericoding/` (99 generated)

**Origin.** Beneficial-AI-Foundation Vericoding Dafny → Aeon
(issue [#194](https://github.com/alcides/aeon/issues/194)).

**Description.** Generated on demand by `translate.py` (not committed). REPORT
cites **~59.6%** pass with `tdsyn_enumerative`.

**Timeout.** `run.py` default **`--budget 30`**; full sweep docs **60s**; outer
subprocess timeout ≈ `budget + 30`.

---

## Suggested defaults by problem class

When a file does not state a budget:

| Class | Suggest |
|---|---|
| Tiny refinement / micro-bench / FTA cell | **5–15s** |
| Classic Z3 / CP assignment / CI-sized | **10–30s** |
| Synquid / AFTA demos / small Boolean GP | **30s** |
| SR (Koza/Pagie/SRBench), SyGuS strings, SMT puzzles, ARC, image edits | **60s** |
| CSG medium+, Mario/dungeon, neuroevolution, AutoNumerics free search | **60–300s** |

---

## Related scripts

| Script | Role | Budget |
|---|---|---|
| `scripts/bench_ortools.py` | OR-Tools vs GP on `examples/synthesis/ortools/` | **5s** |
| `scripts/sygus_to_aeon.py` | Convert SyGuS PBE_SLIA → `afta/sygus/` | N/A |
| `benchmarks/vericoding/run.py` | Translate + synthesize Vericoding tasks | **30s** (default) |

Other `scripts/bench_*.py` files measure LLVM/array/dataframe/Horn performance
and do **not** drive open-ended synthesis search.
