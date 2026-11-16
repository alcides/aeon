# Local bounded Boolean regression fixtures

These 17 cases are hand-written regressions, **not** additional published
BNSynth benchmarks. Each `.ae` file contains the functions to synthesize,
`@bounded_cnf` bounds, relation and universal property. Single-output total
cases additionally use return refinements, including the inconsistent cases.
`sample_trap` intentionally uses a sampled property during baseline search;
the independent verifier still checks its law on every Boolean valuation.

`manifest.json` stores SHA-256 hashes and independent relation truth tables in
lexicographic order (`false` before `true`), with X inputs followed by Y outputs.
Tables describe **allowed coupled tuples**, not one selected output label per
input. They are used only by import verification and the independent checker.
The synthesizer receives only the corresponding Aeon source.

| Cases | Independently established minimum K per output |
|---|---:|
| true, multiple_choices, vacuous | 0 |
| false, identity, not, or, implication | 1 |
| coupled, partial, captured_input, sample_trap | 1 |
| and, equivalence, xor | 2 |
| inconsistent_total, contradictory_total | No solution at K=0,1,2 |

The last two source contracts are inconsistent even without a CNF bound; the
finite-family oracle report deliberately states only the bounds it exhausts.
`partial` and `inconsistent_total` share the relation `x && !y`. The former
states the Skolem implication, imposing no obligation at `x=false`; the latter
has an explicit total return refinement and must fail there.

`oracles.json` enumerates all CNFs made from absent/positive/negative literals,
all clause subsets of size at most K, every output vector, and every Boolean
valuation. It never calls the synthesis backend or Z3. No minimum is inferred
from a timeout or from skipping smaller bounds. Regenerate it with:

```bash
python -m aeon.benchmarks.bounded_boolean oracle \
  --output examples/benchmarks/bnsynth/local/oracles.json
```

Run the fixtures through any compatible backend, retaining all failures:

```bash
python -m aeon.benchmarks.bounded_boolean run --suite local \
  --backend boolean_bounded --bound 2 --budget 2 --wall-timeout 15 \
  --output /tmp/local-bounded-boolean
```

The runner changes only `@bounded_cnf(K)` when choosing another bound. It never
replaces total refinements with a feasibility-domain implication. As in the
published suite, outputs can depend only on X. Regression tests additionally
inject output dependencies, non-CNF expressions, holes, and altered saved
programs, and require independent verification to reject them.
