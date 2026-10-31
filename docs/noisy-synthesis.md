# Noisy-example synthesis

`-s noisy` opts into treating extracted scalar `@example` I/O pairs as soft
observations. Types, refinements, ownership, and termination checks stay hard.
Every candidate is validated before its outputs are observed. The backend
minimizes one scalar objective, rather than a Pareto objective per example:

`J(D,p) = mismatched_rows / total_rows + lambda * executable_complexity(p)`.

```bash
python -m aeon --no-main --budget 5 -s noisy examples/synthesis/noisy/identity.ae
python -m aeon --no-main --budget 5 -s noisy examples/synthesis/noisy/precise.ae
```

The first example permits any nonnegative output. Identity misses one of four
observations and has complexity 1, so its score at default lambda 0.05 is
`0.25 + 0.05 = 0.30`. A larger program fitting the outlier can win at a lower
lambda. The second example requires `v = x`; fitting the outlier is invalid at
every lambda. No candidate or special-case solution is supplied as a fallback.

Missed examples remain failing assertions under `--test` on the completed
program. The report calls these observations *residuals*, not proven bad labels.
Verification proves only the declared contracts, not agreement with every row
or unseen behavior.

## Dataset and objective

Every observation has a zero-based ID in source metadata order. Duplicate inputs
and contradictory expected values remain separate rows with their original
weight. Loss uses exact, typed equality: Bool and Int are distinct, and Float
has no implicit tolerance. NaN, infinity, empty/malformed data, wrong arity/types,
and inputs outside declared preconditions are rejected. Output labels must
have the declared scalar base type; disagreement with the result refinement
does not relax that refinement.

Executable complexity counts each literal, variable, application, lambda, let,
and conditional as one node. Type/refinement applications and annotations cost
zero because they erase at execution. A reference to a source helper/captured
let alias additionally pays for its executable body, recursively, at every
reference. Builtin scalar operators cost one; opaque and recursive helpers are
excluded. Binder IDs and locations do not affect cost. Expansion is bounded at
10,000 nodes and depth 200. Local let bodies are counted at their binding, so
local variables are ordinary one-node references.

Final ranking uses full-data score, then full-data error, complexity, and a stable
structural candidate key. Validation and observation caches are per run; their
keys retain type instantiations and binding identity. No partially scored
candidate can displace a fully scored incumbent.

## Generator and sampling

The generator reuses native bounded enumeration over the scalar result shape;
the original refined type is enforced by the whole-program validator. Each
round adds a bounded number of proposals to its archive and ranks all retained
valid candidates by regularized risk on the current sample. It returns the two
best sample candidates for full scoring. This is an approximate regularized
generator, not an exact empirical-risk minimizer.

Full scoring updates the incumbent and a bounded history Q of loss vectors.
The adaptive sampler minimizes the measured discrepancy
`max(p in Q) abs(R(D,p) - R(S,p))`. Small subset spaces are enumerated exactly;
larger spaces use seeded greedy exchanges and are explicitly reported as
heuristic. Complexity cancels from this discrepancy for a fixed program.
Sample sizes double toward all rows, and may exchange earlier observations.
Budget/round limits can stop growth early. Uniform and full-data modes use the
same generator and resource limits for comparison.

The archive evicts oldest proposals. History evicts oldest fully scored programs
while preserving the incumbent; caches use LRU eviction. The incumbent is held
independently of those bounded stores. Eviction can cause repeated validation
or scoring; counters report actual work, not unique programs.

## Configuration and diagnostics

Use `AEON_SEED` and these environment variables (defaults shown):

| Setting | Default | Meaning |
| --- | ---: | --- |
| `AEON_NOISY_LAMBDA` | 0.05 | Finite nonnegative regularization weight |
| `AEON_NOISY_SAMPLER` | adaptive | `adaptive`, `uniform`, or `full` |
| `AEON_NOISY_INITIAL_SAMPLE` | 2 | Initial row count |
| `AEON_NOISY_ROUNDS` | 8 | Maximum rounds |
| `AEON_NOISY_CANDIDATES_PER_ROUND` | 32 | New proposals per round |
| `AEON_NOISY_ARCHIVE_SIZE` | 128 | Retained proposals |
| `AEON_NOISY_HISTORY_SIZE` | 16 | Fully scored loss vectors |
| `AEON_NOISY_CACHE_SIZE` | 512 | Validation/observation entries |
| `AEON_NOISY_MAX_ROWS` | 10000 | Dataset limit |
| `AEON_NOISY_MAX_DEPTH` | 3 | Native grammar depth |
| `AEON_NOISY_MAX_EXPANSIONS` | 3000 | Native worklist expansions |
| `AEON_NOISY_MAX_WORKLIST` | 5000 | Native worklist capacity |
| `AEON_NOISY_CALL_TIMEOUT` | 1.0 | Seconds per worker operation |
| `AEON_NOISY_EXACT_SUBSETS` | 2000 | Largest exactly searched subset space |
| `AEON_NOISY_EXCHANGE_TRIALS` | 256 | Larger-sample greedy trials |

Generation, domain checking, candidate validation, and observation execution run
in a contained worker. Calls use the smaller of the remaining global budget and
the call limit. A timeout stops the run, kills the worker, and returns only the
already fully scored incumbent; without one, synthesis fails. A crashing or
wrongly typed candidate is invalid, not a noisy observation. Sampling runs in
the coordinator with deadline checks. Process startup, serialization and bounded
teardown add overhead; this is not a hard real-time guarantee.

The terminal prints a concise residual/error/complexity/score summary.
`NoisySynthesizer.last_report.as_dict()` exposes residual row IDs and actual/
expected values, samples, discrepancies, exact/heuristic status, seed, work
counters, elapsed time, and stop reason. The report is an immutable value.

The initial scope is one open scalar body hole with scalar literal I/O equality
examples, including lexical let captures. Opaque/relational examples, ADT data,
coupled open holes, full-function holes, recursion goals, extra optimization
goals, and universal properties are explicit capability errors. Other backends
and the ordinary example test runner retain their behavior; metadata is unchanged.

## Reproduction

```bash
python -m pytest tests/noisy_synthesis_test.py -q
PYTHONPATH=. python scripts/bench_noisy.py --budget 3 --seed 0 --output /tmp/noisy-comparison.json
```

The small comparison uses two development tasks and a separate successor task,
with held-out input checks performed only after synthesis. It records all failed
runs, actual generation/scoring counts, elapsed time, empirical error, and
complexity for equal declared budgets. It is a reproducible diagnostic, not
evidence of general speedups or a generalization bound.

The regularized-generator/history-sampler loop follows the framework in
[Learning Programs from Noisy Data (POPL 2016)](https://files.sri.inf.ethz.ch/website/papers/popl16.pdf).
This bounded Aeon adaptation does not reproduce BITSYN, DEEPSYN, or their
published results, and makes no exact-generator or optimality guarantee.
