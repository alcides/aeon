# BNSynth benchmarks in Aeon

These are **38 published artifact specifications**, translated to ordinary Aeon
files with source-defined relations, holes, CNF bounds and property laws. They
can be given to any compatible Aeon synthesizer. No benchmark-specific search
code, Python `native` specification, neural model or reference solution is used.

```bash
python -m aeon --no-main --budget 5 -s random_search \
  examples/synthesis/boolean_bounded/bnsynth/cases/misc1_2_1.ae
python -m aeon --no-main --budget 5 -s smt \
  examples/synthesis/boolean_bounded/bnsynth/cases/misc1_2_1.ae
python -m aeon --no-main --budget 5 -s boolean_bounded \
  examples/synthesis/boolean_bounded/bnsynth/cases/lut1_2_2.ae
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
separate Boolean interpreter. Tests evaluate returned Aeon terms as well.
`verify` checks the saved certificate against the original relation; it does not
trust the synthesizer's reported fitness or its own verification routine.

The runner isolates every attempt in a subprocess. The default total wall limit
is synthesis budget + 30 seconds for startup, parsing and checking; override
`--wall-timeout`. It kills the worker's process group, including fitness workers,
on timeout. POSIX workers also have a default 4096 MiB address-space limit
(`--memory-mb`) and a CPU limit. Other platforms retain wall-time containment.
Resume keys include case/source hashes, backend, K, seed, budgets, memory limit,
Python version, Aeon revision and a hash of all Aeon Python sources. Use
`--no-resume` to repeat matching runs. Results from different bounds or code are
never reused as the same attempt.

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
not establish minimum K. These Aeon algorithms differ from the paper's neural
learner; the included coverage report is a smoke evaluation, not a reproduction
of its performance claims.

## Recorded smoke coverage

[coverage.json](coverage.json) retains every attempt, timings, source/code hashes,
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
report = json.loads(Path("examples/synthesis/boolean_bounded/bnsynth/coverage.json").read_text())
result = next(r for r in report["reports"]["full_corpus"]["results"] if r["status"] == "verified_solved")
Path("/tmp/bnsynth-candidate.json").write_text(json.dumps(result))
PY
python -m aeon.benchmarks.bounded_boolean verify /tmp/bnsynth-candidate.json
```

Run regression tests with:

```bash
pytest tests/bounded_boolean_benchmarks_test.py tests/boolean_bounded_test.py
```
