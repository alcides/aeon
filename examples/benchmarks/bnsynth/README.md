# BNSynth benchmarks in Aeon

These are **38 published artifact specifications**, translated to ordinary Aeon
files with source-defined relations, holes, CNF bounds and property laws. They
can be given to any compatible Aeon synthesizer. No benchmark-specific search
code, Python `native` specification, neural model or reference solution is used.

```bash
python -m aeon --no-main --budget 5 -s random_search \
  examples/benchmarks/bnsynth/cases/misc1_2_1.ae
python -m aeon --no-main --budget 5 -s smt \
  examples/benchmarks/bnsynth/cases/misc1_2_1.ae
python -m aeon --no-main --budget 5 -s boolean_bounded \
  examples/benchmarks/bnsynth/cases/lut1_2_2.ae
python -m aeon --no-main --budget 10 -s bnsynth \
  examples/benchmarks/bnsynth/cases/lut1_2_2.ae
```

Use the benchmark runner below for claims of success: a baseline's sampled
property score or ordinary typecheck alone does not prove the universal law.

## Provenance and inventory

Source: [BNSynth: Bounded Boolean Functional Synthesis](https://arxiv.org/abs/2212.08170),
[artifact revision 12a12dab](https://github.com/rrlcs/bnsynth/tree/12a12dab2f3ed8ff92f88dc8a915826a8f9fe6d4).
The paper reports 19 custom and 7 LUT cases; this import includes all 38 available
Verilog specifications in the pinned artifact, including its additional cases.
The LUT problems derive from EPFL/ISCAS85 circuits.

`upstream/` preserves original bytes, including the MIT license and the upstream
README, experiment driver, shell script and preprocessing utilities for provenance.
They are data for this suite: none is executed. `manifest.json` pins each file's
SHA-256, source/generated-file mapping, variable partitions/order, unused
signals, per-function bound and generated-source hash. The upstream files are
excluded from formatting hooks to preserve those hashes.

There are **53 benchmark Y lists**, **38 matching specifications**, and **15
orphan lists**, all named in the manifest. Another **52 lists** accompany
reference solutions under `experiments/manthan_skfs/Yvarlist/`; their paths and
Git blob IDs are recorded in `inventory-provenance.json` and excluded from the
corpus. Thus the repository-wide count is 105 lists, but **not 105 benchmark
instances**. This corrects the directory/count interpretation in issue #650.
Neither the orphan lists nor reference solutions become synthesis tasks.
All 67 lists without a published specification (15 orphans plus 52 reference
lists) are now explicitly enumerated together in the manifest, with their
categories retained. The inventory provenance file has its own SHA-256 pin.

The importer accepts scalar combinational modules with input/output/wire
declarations, continuous assignments, constants, parentheses, negation, AND,
OR and XOR. It checks precedence, drivers, references, cycles, ports and Y
partitions, and rejects unsupported syntax with a filename and line. It retains
sharing through Aeon `let` bindings and drops only unreachable circuit logic;
unused wire declarations never become unconstrained inputs.

## Problem semantics and bounds

For a relation `F(X,Y)`, the source states the Skolem law:

```text
forall X,Y. F(X,Y) => F(X, choose(X))
```

The Verilog module's `out` is the relation predicate, not a synthesis output.
The Y list identifies which *input ports* are replaced by synthesized functions.
For example, `lut1_2_2` has X=`i0,i1` and Y=`i2,i3`. The two unknown functions each
receive only `i0,i1`; `i2,i3` appear as witnesses in the property. This follows
upstream `code/utils/utils.py`: `prepare_file_names` selects the Y list and
`create_error_formula` compares the original relation output with the relation
under the synthesized outputs. No unate optimization or executable upstream
preprocessing is necessary to preserve the original problem.

Unknown functions precede the relation definition, so the specification cannot
be used as a synthesis component. There are no expected solutions in their scope.
Partial/don't-care domains and coupled output choices are preserved without
constructing exponential truth tables or weakening arbitrary total refinements.

Each checked-in file uses `@bounded_cnf(5)` on every output. This is a uniform
starting bound, **not an assertion of satisfiability or minimum K**. The runner's
`--bound` explicitly regenerates the same source variant for every backend,
saves it, and records its hash. K counts normalized CNF clauses: true has zero;
false has one empty clause. Duplicate clauses/literals and tautologies are
removed. Only input literals are accepted; helpers, witnesses, conditionals and
non-CNF expressions cannot masquerade as one clause. No auxiliary inputs are
introduced. These are feasibility benchmarks; smaller K is a separate run,
not an optimization objective hidden in Python.

`boolean_bounded` checks compiler obligations universally. Existing joint
backends (`random_search`, `gp`, `smt`, `sygus`) can consume the same files with
their existing algorithms. Single-hole backends such as `enumerative` can run
single-output cases; adapters without joint/hard-bound support report
unsupported for other cases. Search may time out or return a candidate that
fails exact checking; these outcomes remain in the results. SyGuS requires its
existing optional CVC5 dependency.

## Reproduce, run and verify

The corpus is vendored; normal use and tests need no network access.

```bash
# Check source/generated hashes and show inventory.
python -m aeon.benchmarks.bounded_boolean inventory
# Rebuild all ordinary .ae files and the manifest deterministically.
python -m aeon.benchmarks.bounded_boolean import
# Explicit optional fetch/repair of pinned, SHA-256-checked upstream files.
python -m aeon.benchmarks.bounded_boolean fetch
# Independently prove every generated Aeon relation equivalent to its Verilog.
python -m aeon.benchmarks.bounded_boolean audit --output /tmp/bnsynth-audit

# Identical cases/bounds/seeds/budgets for multiple synthesizers.
python -m aeon.benchmarks.bounded_boolean run \
  --case misc1_2_1 --case lut1_2_2 \
  --backend boolean_bounded --backend random_search --backend smt --backend gp \
  --bound 5 --budget 5 --seed 0 --seed 1 --output /tmp/bnsynth-comparison

# Omit --case to attempt all 38; every failure stays in the denominator.
python -m aeon.benchmarks.bounded_boolean run \
  --backend boolean_bounded --bound 5 --budget 5 --output /tmp/bnsynth-all
# Recheck a saved candidate using fresh solver state and original source bytes.
python -m aeon.benchmarks.bounded_boolean verify /tmp/bnsynth-all/RUN_KEY.json
```

Each run saves its source variant, candidate `.ae` file (when available), portable
CNF certificate, diagnostics and JSON result. A candidate file is not necessarily
correct: inspect `status`. The checker validates signatures/dependencies and CNF
shape independently of the synthesis backend, then translates the **original
Verilog** to Z3 and checks `F(X,Y) && !F(X, choose(X))` for unsatisfiability.
It also checks domains up to eight original input ports exhaustively using a
separate Boolean interpreter, and executes the actual returned Aeon function
terms on every input in those small domains to cross-check extraction.
`verify` checks the saved certificate **and the saved `.ae` program**: file hash,
parsing, Aeon typechecking, output signatures, CNF extraction, agreement with the
certificate, relation equivalence, and small-domain execution. An altered or
missing candidate file fails verification. Resume also checks the saved source
and candidate files before reusing a result. Neither step trusts reported fitness.

The runner isolates every attempt in a subprocess. The default total wall limit
is synthesis budget + 30 seconds for startup, parsing and checking; override
`--wall-timeout`. It kills the worker's process group, including fitness workers,
on timeout. POSIX workers also have a default 4096 MiB address-space limit
(`--memory-mb`) and a CPU limit. Other platforms retain wall-time containment.
Resume keys include case/source hashes, backend, K, seed, budgets, memory limit,
Python version, Aeon revision and a hash of all Aeon Python sources. Use
`--no-resume` to repeat matching runs. Results from different bounds or code are
never reused as the same attempt.
Circuit parsing and candidate serialization run inside the limited worker.
Source preparation has its own timing, and import failures remain in the
attempt denominator instead of aborting the remaining cases.

`summary.json` retains all attempts, per-backend status counts and individual
results. Statuses distinguish verified solutions, reported bounded UNSAT,
timeout/resource limit, unknown, unsupported/unavailable, no solution/search
failure, translation/type/semantic/structural failures, bound violations and
internal/worker errors. Parse, import verification, synthesis, final verification
and total times are separate. Available backend iteration/counterexample counts,
clause/literal counts and candidate hashes are retained. Small bounded-UNSAT
claims are checked by an independent finite-family enumeration when affordable;
other claims are labelled uncertified. Timeout is never reported as UNSAT.

`--paper-schedule` optionally runs the upstream sequence of (K, seconds):
(1,60), (5,120), (20,120), (50,180), (500,300), (1000,600), stopping after the
first independently verified solution. The first successful scheduled K does
not establish minimum K. `bnsynth` implements the paper's gated neural CNF
learner and counterexample loop, using Aeon VCs and Z3 sampling/verification;
install `AeonLang[synthesis-bnsynth]`. `boolean_bounded` is a separate SAT-template
algorithm. Sampling, timing and simplification differ from the reference tool,
so these reports are smoke evaluations, not reproductions of its measurements.

## Recorded smoke coverage

**Historical report correction:** `coverage.json` and `validation.json` predate
the exact-application-identity fix. Their `lut7-ctrl_7_1` bounded-UNSAT report at
K=5 is incorrect. Ordinary typechecking dropped call equations above its
64-node singleton limit; treating the remaining stronger VCs as exact made the
synthesis problem falsely infeasible. Synthesis now retains these equations.
An independent five-clause, eleven-literal certificate and a successful solver
run are covered by `tests/boolean_bounded_precision_test.py`. Historical reports
are retained as records; their uncertified UNSAT claims are not ground truth.

[neural-validation.json](neural-validation.json) records the corrected solver
run and the new neural backend, with source hashes, reproduction commands and
portable candidate certificates:

| Backend | K | Synthesis budget per case | Verified / 38 | Other outcomes |
| --- | ---: | ---: | ---: | --- |
| `boolean_bounded`, after the identity fix | 5 | 2 s | 22 | 7 bounded-UNSAT reports, 9 timeouts |
| `bnsynth`, neural learner | 5 | 10 s | 16 | 22 timeouts |
| `bnsynth`, neural learner | 5 | 1,800 s | 20 | 18 timeouts |

[neural-30min.json](neural-30min.json) records the completed longer run from
17 November 2026: all 38 cases, seed=0, eight concurrent single-threaded
learners on `polaris`, with a 1,800-second synthesis limit and 1,830-second
outer limit per case. All successful programs were independently verified.
The run took about 90 minutes overall. It used commit `4627b97d` before this
PR was rebased; its original revision and implementation hash remain in the
report. Concurrency and single-seed sampling limit timing comparisons.

The four additional successes were:

| Case | Synthesis time | Maximum clauses per output |
| --- | ---: | ---: |
| `lut4-c17b_5_2` | 20.6 s | 5 |
| `xor_4_3` | 26.2 s | 5 |
| `lut6-c17d_5_2` | 91.3 s | 5 |
| `lut7-ctrl_7_1` | 119.8 s | 5 |

No further solutions appeared after two minutes. Timeouts are not proofs of
infeasibility at K=5. Repeat the same per-case configuration sequentially with:

```bash
python -m aeon.benchmarks.bounded_boolean run \
  --backend bnsynth --bound 5 --budget 1800 --wall-timeout 1830 \
  --seed 0 --output /tmp/bnsynth-30min
```

The corrected solver also solved `lut7-ctrl_7_1` within a separate 10-second
budget (about 5.7 seconds of synthesis in that run). These unequal budgets and
single seeds are executable coverage, not a ranking. The neural run includes
PyTorch initialization and never reports bounded UNSAT. Archived certificates
can be rechecked explicitly with `verify RESULT.json --certificate-only`;
rerun the commands to retain and verify the complete candidate `.ae` files.

[coverage.json](coverage.json) is the original smoke report. It retains every attempt, timings, source/code hashes,
portable candidate certificates and reproduction commands. All **38/38** imports
passed the independent equivalence check. With K=5, seed=0, a two-second synthesis
budget and a ten-second total wall limit, `boolean_bounded` produced **23 verified
solutions**, **8 reported bounded-UNSAT results** and **7 timeouts** across all
38 cases. Those eight infeasibility reports are explicitly **not independently
certified**.

The same three cases (`misc1_2_1`, `lut1_2_2`, `misc2_3_1`) were also run through
six backends with identical inputs, bounds and limits:

| Backend | Verified / attempted | Other outcomes |
|---|---:|---|
| `boolean_bounded` | 3 / 3 | — |
| `random_search` | 3 / 3 | — |
| `smt` | 2 / 3 | 1 search failure |
| `gp` | 2 / 3 | 1 no solution |
| `enumerative` | 2 / 3 | 1 unsupported multi-output task |
| `sygus` | 1 / 3 | 2 candidates rejected by the independent semantic check |

These short runs establish executable coverage; they are too small for performance
rankings. The report records the parent Git commit and the hash of the actual
uncommitted Aeon Python sources used. Source/candidate filenames from temporary
run directories are omitted from the archive; certificates are embedded. To
recheck an archived solution, extract one result and use the same verifier:

```bash
python - <<'PY'
import json
from pathlib import Path
report = json.loads(Path("examples/benchmarks/bnsynth/coverage.json").read_text())
result = next(r for r in report["reports"]["full_corpus"]["results"] if r["status"] == "verified_solved")
Path("/tmp/bnsynth-candidate.json").write_text(json.dumps(result))
PY
python -m aeon.benchmarks.bounded_boolean verify /tmp/bnsynth-candidate.json
```

Run regression tests with:

```bash
pytest tests/bounded_boolean_benchmarks_test.py tests/boolean_bounded_test.py
```

## Local exhaustive regression suite

The [17 local fixtures](local/README.md) are separate from the published corpus.
They cover constants/nullary functions, identity, negation, AND, OR, implication,
equivalence, XOR, coupled outputs, multiple valid outputs, partial feasibility,
vacuity, inconsistent total refinements, lexical captures, and a candidate that
can pass samples but fails exact verification. Their specifications remain in
ordinary `.ae` files; independent truth tables live in `local/manifest.json` and
are never exposed to synthesis backends as labels, hints or helper functions.

```bash
# Independently enumerate every local CNF family at K=0,1,2; no synthesis/SMT.
python -m aeon.benchmarks.bounded_boolean oracle --output /tmp/local-oracles.json
# Compare a backend against the same explicit total/partial Aeon contracts.
python -m aeon.benchmarks.bounded_boolean run --suite local \
  --bound 2 --budget 2 --wall-timeout 15 --output /tmp/local-boolean-runs
pytest tests/bounded_boolean_local_test.py tests/bounded_boolean_benchmarks_test.py \
  tests/boolean_bounded_test.py tests/boolean_bounded_timeout_test.py
```

[`local/oracles.json`](local/oracles.json) certifies expected minimum K values
from complete enumeration, including XOR's K=1 failure and K=2 success. Total
refinements are checked on **every** input; they never acquire partial-relation
don't-care semantics. Resource-limited enumeration returns `not_checked`, never
UNSAT. An unsolved large published case still has no independently certified
minimum or infeasibility claim.

[`validation.json`](validation.json) records the fresh published import audit,
full-corpus smoke run, and the separate local K=0,1,2 runs for this completion of
#650. It retains all outcomes and the exact implementation/source hashes used.
The published run verified 23 solutions, retained 8 uncertified bounded-UNSAT
claims and 7 timeouts. All 51 local case/bound combinations matched their
oracles: 30 verified solutions and 21 exhaustively certified bounded-UNSAT
results. Every solved candidate's saved `.ae` program was rechecked before
archiving its certificate.
Its archived certificates can be rechecked with `verify --certificate-only`;
that mode explicitly reports `verification_scope: certificate_only` and makes
no claim to have checked an absent `.ae` file. Normal live runs use schema 2 and
require their adjacent candidate files. Older schema-1 certificate archives
remain readable and are also labelled with this narrower verification scope.
