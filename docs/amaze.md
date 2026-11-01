# AMaze: standard-library-trained grammar optimization

`-s amaze` uses a learned, additions-only grammar in a finite typed enumerator.
Its offline trainer mines compositions from Aeon's packaged standard library,
models enumeration cost, searches grammar additions, and periodically reruns
stdlib reconstruction tasks. Inference loads the resulting JSON profile and
expands every macro into ordinary Aeon Core syntax before normal whole-program
validation and objective evaluation.

The implementation follows the rank-based grammar-optimization approach in
[Ye et al., *Accelerating Syntax-Guided Program Synthesis by Optimizing
Domain-Specific Languages*, POPL 2026](https://xinpl.github.io/papers/popl26b.pdf).
This adapter enumerates complete expressions. Its feature component is therefore
the complete expression; it does not claim the fragment decomposition of the
paper's DryadSynth, Duet, PolyGen or EUsolver adapters. There is no GP or cvc5
integration and no production deletion mode.

## Run and train

A versioned profile is included in the package:

```bash
python -m aeon --budget 10 -s amaze examples/synthesis/amaze/guard.ae
python -m aeon.synthesis.modules.amaze inspect \
  aeon/synthesis/modules/amaze/stdlib-profile.json

# Explicit offline learning; no user program or alternate training root.
python -m aeon.synthesis.modules.amaze train-stdlib \
  --output /tmp/amaze-stdlib.json --seed 0 --budget 90 \
  --task-budget 2 --max-candidates 20000 --max-cost 9
AEON_AMAZE_PROFILE=/tmp/amaze-stdlib.json python -m aeon \
  --budget 10 -s amaze examples/synthesis/amaze/guard.ae
```

The trainer accepts an output path, seed and bounded resource settings; there is
no `--training-dir`. It runs in a subprocess with a total wall limit, and on POSIX
with a 4 GiB address-space limit and a CPU limit. Each reconstruction also has a
wall limit, cost limit and candidate limit. Search has iteration, pattern and
selected-production limits. Budgets/limits and censored runs are recorded in the
profile. Failed collection/training cannot silently produce random model weights
or use an external corpus.

## Learning boundary and supported subset

The canonical corpus is the installed package's `aeon/libraries/**/*.ae`.
Collection records every canonical source path and SHA-256, dependencies and their
hashes, every source definition's eligibility or skip reason, and every training
label's originating function. Imports use a session-local package-only resolver:
no cwd, local `libraries`, `AEONPATH` or disk compilation-cache overrides enter
training. Symlinks escaping the canonical root are rejected. Normal compiler
resolution outside that session is unchanged.

The initial subset is total, first-order, unrestricted, monomorphic Int/Bool
functions with one to three scalar arguments. Pure conditionals, supported
primitive arithmetic/comparison/Boolean operators, constants 0/1/false/true and
pure lets are supported. Native wrappers, effects, recursion, opaque helper
calls, ADTs, float/string functions, polymorphism, abstract refinements, refined
training signatures and non-default multiplicities are explicitly skipped.
This is a small-corpus pilot: the current library supplies **9 eligible functions
(8 alpha-distinct groups)** from `Refinement` and `Vec`, out of 1,215 source
definitions. The remaining 1,206 definitions have recorded skip reasons.

Eligible original AST/source spans are compiled in isolated compiler sessions.
Only a preflight-audited pure definition is compiled; unrelated module code,
native strings and effectful initializers are never executed. Deterministic
Cartesian probes over `[-2,-1,0,1,2]` / Booleans are evaluated from the real Core
reference implementation and cross-checked against the grammar interpreter.
A candidate must match those probes, prove universal equality to the reference
with Z3, and pass ordinary Aeon typechecking. Weak result types alone cannot
count as reconstruction success. Unknown verification results are failures to
establish reconstruction. Neither the target function nor any self-alias is in
the reconstruction grammar, and the reference body is never injected as a search
candidate or fallback.

Seeded splits group alpha-equivalent reference bodies/signatures before mining.
The current split has 5 training functions, 2 validation functions and 2 held-out
functions. The synonymous `positive` and `non_empty_size` stay in one group and
count as one independent support group for mining. Only training bodies supply
macros, known solutions, model-fitting labels and periodic synthesis feedback.
Validation chooses ridge regularization and the retained grammar. Held-out data
is inspected for final evaluation after freezing selection/model parameters;
it never supplies patterns, labels for fitting, or DSL-selection decisions.

Inference can use local Int/Bool variables and concrete refinements, with the
full original typing obligations retained by the validator. Opaque helpers and
unsupported types do not become grammar productions. Unsupported goal types
fail explicitly. Existing objective/Pareto semantics use the shared candidate
driver; multi-hole and hard-constraint capability checks remain with the ordinary
entrypoint. Inference never mines user bodies, updates cost parameters, records
new training solutions, writes the profile, or trains on a cache miss.

## Grammar, counting and search

Each production has a stable ID, input/result sorts, a positive integer cost,
and a closed expansion template. Base productions are a separately recorded
fixed set of language primitives. Learned patterns are bounded repeated
subtree/frontier compositions from training references, with alpha-normalized,
typed parameters. Repeated identical variables or subexpressions map to the same
parameter. A pattern like `double(p) = p + p` has **one** enumerated argument.
Templates cannot contain user/global names, native code or executable payloads.
All arguments are pure and total; expansion preserves their value semantics.

Enumeration order is increasing derivation cost, production ID, argument-cost
composition, then mixed-radix child rank. This is a new first-order adapter,
not the existing action/worklist BFS with an assumed CFG ordering. It directly
consumes the selected grammar. Unranking generates real candidates without
materializing all smaller trees. DP memoizes counts by sort/cost within each
immutable grammar instance; positive production costs make recursive grammars
well-founded. Zero/negative costs are rejected, empty/unproductive nonterminals
count zero, and Python integers avoid fixed-width overflow.

The rank estimate is the cumulative number of **derivations** through the best
rewrite's cost. It is an upper bound on that expression's first discovery, not
an exact position, distinct-AST count or observational-equivalence count.
Ambiguous macro/base derivations deliberately remain in both counting and
search. A recursive matcher finds the minimum-cost supported rewrite while
preserving tied-parameter equality. Tiny exhaustive-enumeration tests compare
counts, unranking order and rewriting, including ambiguous grammars and counts
larger than machine integers.

The trainer fits log-cost ridge models for candidate counts and elapsed time
from actual reconstruction runs. A successful run supplies a measured cost;
a timeout/limit supplies a lower bound with one-sided squared loss. Censored
runs are never fabricated successes. Candidate-count predictions drive a
bounded deterministic hill-climber over additions; elapsed-time predictions are
reported separately. For each proposal, DP estimates the best rank among the
known stdlib solutions for each training task. Proposal scoring does not rerun
the synthesizer. After an accepted addition, real stdlib training synthesis
refreshes the solution archive and refits both models. Real validation runs
select the best retained profile. All original productions remain available.

## Profile and measurements

[`stdlib-profile.json`](../aeon/synthesis/modules/amaze/stdlib-profile.json)
contains the schema, primitive signatures, grammar/feature versions, source and
dependency manifest, split IDs, typed patterns and their source-function lineage,
selected production IDs, fitted coefficients, configuration, all measurements,
proposal scores, refresh history, known solutions and held-out comparison.
It is data-only JSON and is loaded into frozen records. Loading checks schema,
primitive signatures, source inventory/hashes, template typing and lineage.
Relocating an installation is supported when relative source paths and hashes
match; missing/stale/incompatible profiles require explicit stdlib retraining.

The recorded 20,000-candidate experiment selected one macro equivalent to
`(a <= b) && c`. Initially 2/5 training functions solved; after the refresh,
4/5 solved, including `in_range` and `bounded`. The two held-out predicates both
solved under both grammars at **39 and 35 candidates**, respectively. There is
**no held-out candidate-count improvement** in this small experiment, and the
measured times do not establish a speedup. Per-task times, validation failures,
censored counts and total offline time are in the artifact. The paper's reported
speedups are not claims about this adapter.

| Recorded run | Solved / attempted | Candidates, including censored runs | Reconstruction seconds |
|---|---:|---:|---:|
| Training, original grammar | 2 / 5 | 60,060 | 2.2966 |
| Training, selected addition | 4 / 5 | 42,527 | 1.5964 |
| Held-out, original grammar | 2 / 2 | 74 | 0.00677 |
| Held-out, selected addition | 2 / 2 | 74 | 0.00682 |

All four rows recorded zero validation failures. Total offline collection,
fitting, search and evaluation took 6.14 seconds on this run. The complete JSON
profile, including all skipped-definition records and measurements, is 390,598
bytes (about 381 KiB). Times are observations from one small run, not stable
performance estimates.

Inference logs the profile/stdlib hashes, available productions/macros,
enumerated macro IDs, cumulative rank bound of the last searched cost, actual
candidate count, validation failures, elapsed time and stop reason. No hidden
fallback occurs: the optimized grammar always includes its original primitives.

```bash
pytest tests/amaze_test.py
```
