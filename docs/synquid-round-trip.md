# Synquid round-trip checking and liquid abduction

The `synquid` backend follows the checking/strengthening distinction in
[Polikarpova, Kuraj and Solar-Lezama, PLDI 2016, §§3.2–3.6](https://cseweb.ucsd.edu/~npolikarpova/publications/pldi16.pdf).
The implementation keeps Aeon's existing whole-program refinement and
termination verifier as the final acceptance gate.

## Constraint lifecycle

`ConstraintState` owns a branch's typing context, precise contextual witnesses,
subtyping VCs, pending result obligations, type assignments, predicate
vocabularies, and alternative liquid assignments. `fork()` copies mutable
assignments; immutable obligation tuples are shared. Sibling alternatives and
opposite branch paths cannot inherit each other's mutations. Search deliberately
disables the former `(context, level, goal)` term cache.

`ApplicationState` implements the application spine rules. It propagates
result-shape information into polymorphic types, with fresh refinement
unknowns. Constraints on datatype element types are available immediately.
Result obligations mentioning an unchosen formal are retained until that
argument exists. A chosen first-order argument contributes its inference VC
and precise type; existential binders are opened into the branch context.
Literal/variable substitution continues to narrow later dependent parameters.
Other expressions use a fresh contextual witness. Higher-order arguments are
checked without treating functions as scalar SMT values, and can be delayed
until the first-order arguments determine their requirements.

Type variables absent from the result acquire shapes from argument candidates.
Their candidate shapes come from in-scope scalar values plus primitive literal
shapes, within the existing depth bound; this is not unrestricted higher-kinded
unification. A repeated result type variable collects qualifiers from all its
occurrences. Abstract-refinement parameters use their declared argument sorts
and the existing finite qualifier generator. Explicit solved liquid type
arguments remain in emitted core terms. Implicit abstract-refinement applications
are checked again by the final verifier using its existing inference.

Consistency uses the existing VC lifting and SMT translation, including declared
measure contracts, datatype encodings and path assumptions. For example, an
append result of length five is inconsistent with a prefix of length six and
any suffix with nonnegative length. The suffix generator is never opened.
Consistency is existential and only necessary: satisfying it does not establish
subtyping or approve a completed program.

## Weakest-condition solving

`solver.py` is a synthesis-specific greatest-fixpoint solver. It starts fresh
predicates at `true`, then strengthens negative occurrences to discharge new
Horn clauses. The verification solver in `verification/horn.py` is unchanged.

Strengthening enumerates minimal unsatisfiable subsets relative to the fixed
negated conclusion. It uses MARCO's Boolean subset map: shrink a successful seed
to a minimal subset and block its supersets; grow a failing seed to a maximal
satisfiable subset and block its subsets. Minimization uses validity queries
rather than a solver-specific unsat-core API. This is an oracle implementation
of MUSFIX's finite-subset search, not enumeration of guard/branch products.
Conjunctions have no fixed width limit. Alternative minimal strengthenings are
retained when later obligations require backtracking. Guard solutions are also
compared semantically: equivalent guards collapse and strictly stronger guards
are discarded; incomparable weakest guards remain separate.

IFAB introduces the unknown path predicate before constructing the proposed
branch. Thus a callee precondition inside that branch can itself constrain the
path. After solving the complete branch VC, search constructs the Boolean guard
and synthesizes the other branch under its negation. Predicate valuations must
have an inhabitant in their creation scope; contradictory guards and
inconsistent starting contexts cannot manufacture successful abductions.

## Supported fragments and bounds

- Application queries reuse Aeon's first-order refinement language, scalar and
  datatype sorts, measures, existing existential representation, and function
  subtyping. Unsupported or undecidable obligations remain for final checking.
- Guard realization currently uses the existing in-scope integer relational
  vocabulary, including constants and templates harvested from specifications.
  It instantiates polymorphic relational operators explicitly. More complex
  Boolean programs and arbitrary function inverses are not inferred.
- Guard vocabulary is capped at 48 atoms; each conditional proposes at most 64
  branches per level. MUS enumeration has a default 256-query bound per
  strengthening and 256 explored valuations per solve. Individual SMT queries
  have a 100 ms timeout. The overall synthesis deadline is checked during
  construction and solving.
- `valid`, `invalid`, `unknown`, `unsupported`, `qualifiers exhausted`, and
  `inconsistent context` are distinct outcomes. Unknown/timeouts and unsupported
  sorts do not justify logical pruning. Exhaustion means failure within the
  finite vocabulary, not a proof that no program exists.
- Outside successful abduction, search retains bounded one- through four-atom
  qualifier-conjunction enumeration. Both branches still receive their path
  assumptions. Core `match`/`fix` synthesis, arbitrary recursive invariants,
  unbounded shape discovery, and full PLDI benchmark coverage are not claimed.

## Reproducible validation

From an environment with Aeon's development dependencies:

```bash
python -m pytest tests/synquid*test.py tests/partial_vc_test.py
python scripts/bench_synquid_round_trip.py
pre-commit run --all-files
python -m aeon --budget 3 -s synquid --no-main examples/synthesis/synquid/List-Append.ae
python -m aeon --budget 3 -s synquid --no-main examples/synthesis/synquid/List-Null.ae
python -m aeon --budget 3 -s synquid --no-main examples/synthesis/synquid/StrictIncList-Insert.ae
```

The counter script fixes a finite grammar: one prefix and eight nonnegative
suffix lengths, with desired result length five. It instruments the argument
generator and final-verifier calls independently of the backend's own counters.
Run the same script against baseline commit `5a0821b9` by setting `PYTHONPATH` to
a checkout of that commit.

| Fixture / revision | Argument candidates | Suffix generators | Partial rejections | Complete local rejections | Full validations | Verified solutions |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Prefix length 6 / baseline | 9 | 1 | 0 | 0 | 8 | 0 |
| Prefix length 6 / round-trip | 1 | 0 | 1 | 0 | 0 | 0 |
| Prefix length 3 / baseline | 9 | 1 | 0 | 0 | 8 | 1 |
| Prefix length 3 / round-trip | 9 | 1 | 0 | 7 | 1 | 1 |

These counts measure early pruning, not wall-clock speed. Tests also compare
all verified solutions in a small exhaustive grammar, check dependent
arguments and fork isolation, and verify weakest `max(x,y)` guards against a
finite qualifier vocabulary.

The end-to-end recursive fixture builds a measured `Nat` value of the requested
size. It synthesizes the decreasing recursive call and verifies the substituted
whole program. Adding an unused non-decreasing call preserves the result's
refinement but fails the existing termination check.

In the three-second benchmark sample, `StrictIncList-Insert` succeeds with the
unchanged specification; its existing length requirement admits returning the
input. `List-Append` and `List-Null` exhaust that budget. These are bounded-search
results, not evidence of a complete implementation of the original benchmark
suite. No benchmark specification is weakened for these measurements.
