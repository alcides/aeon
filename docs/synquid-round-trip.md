# Synquid round-trip checking and synthesis

The `synquid` backend implements the search rules in
[Polikarpova, Kuraj and Solar-Lezama, PLDI 2016, §§3.2–3.7](https://cseweb.ucsd.edu/~npolikarpova/publications/pldi16.pdf),
adapted to Aeon's core terms and verifier. Construction discharges refinement
and termination obligations before emitting candidates. Synquid does not rerun
whole-program typechecking for each candidate; non-type specifications and
objective evaluation still use the shared adapters.

## Search rules

The default `synquid_search: "paper"` streams candidates at increasing
application-depth bounds. At function goals it introduces a decreasing recursive
hypothesis (FIX), type abstractions (TABS), and value abstractions (ABS).
Termination weakening uses a lexicographic tuple of the eligible arguments:
nonnegative integers and declared integer datatype measures. Structural-rank
measures take priority over size and other measures. Recursive arguments must
prove nonnegativity and strict lexicographic decrease; measures are never assumed
positive without a proof. Generated fixpoints carry explicit `decreasing_by`
metrics and pass the ordinary termination verifier.

For a hole occupying a surface function's body, the backend recovers the enclosing
schema, synthesizes a local function, and applies it to the existing parameters.
This allows FIX and TABS without rewriting the outer declaration. Holes already
inside `@allow_recursion` definitions receive recursive hypotheses weakened by
the source's explicit termination metrics. Without a metric, recursive return
refinements are erased as in the core checker.

At scalar goals the engine enumerates elimination terms (variables, literals,
and applications), checking partial applications as it constructs them. It tries
unconditional solutions first, then IFAB: propose a branch under an unknown path
predicate, solve for that predicate, construct an executable Boolean guard, and
synthesize the remaining branch under its negation. Executable atoms are realized
directly, as in the original Synquid implementation; other guards are synthesis
subgoals of type `{b:Bool | b = condition}`. Nested conditionals retain the
application-depth bound. Both path regions must be proved nonempty before
recursive expansion, so each conditional removes a nonempty qualifier region.
There is no independent conditional-depth bound.

Match abduction first tries scalar-constructor facts for in-scope datatype
variables. General MATCH remains the fallback, including datatypes without
scalar constructors and scrutinees computed by applications. Matches lower to
Aeon's existing datatype eliminators. Each handler receives the constructor's
field types, result refinements, and exact constructor equation. Computed
scrutinees are let-bound so checking and termination analysis share the same
witness. `synquid_match_depth` bounds match nesting independently (default: 2).

MATCH retains the scrutinee's refined type arguments, including nested and
abstract element refinements. Eliminator predicate parameters are fresh liquid
unknowns, constrained together across all handlers and emitted as explicit
predicate arguments after solving. The verifier also infers omitted match
predicates instead of fixing them to `true`.

Datatype predicate arguments are retained separately from element types. For
example, `(Duo a){|r|}` stores the binary relation `r`; matching that value
instantiates its constructor fields with the stored relation. Erasing a relation
is allowed, but an erased value cannot be strengthened back to an indexed one.
Explicit relation arguments are invariant: subtyping proves pointwise equivalence
on the element domain. Variance inference for predicate parameters is not implemented.

Legacy datatypes whose constructor results omit predicate arguments keep their
previous behavior. An absent predicate must follow from the actual fields and
constructor equations before matching can assume it. In particular, an explicit
`false` predicate cannot make a branch vacuously correct.

## Abstract refinements: runnable examples

[abstract_identity.ae](../examples/synthesis/synquid/abstract_identity.ae) exercises
unary predicate polymorphism. The new
[relational_swap.ae](../examples/synthesis/synquid/relational_swap.ae) synthesizes a
transformation of an arbitrary binary relation:

```aeon
inductive Duo a forall <r:a -> a -> Bool>
| mk (first:a) (second:{v:a | r first v}) : (Duo a){|r|}

def swap : forall a:B, forall <r:a -> a -> Bool>,
    (d:(Duo a){|r|}) -> (Duo a){|fun x => fun y => r y x|} := ?body;
```

```bash
python -m aeon --budget 30 -s synquid examples/synthesis/synquid/relational_swap.ae
```

Synquid synthesizes a match that constructs `Duo.mk second first`. The result
passes whole-program validation for arbitrary `a` and `r`. Its concrete `main`
returns `(2, 1)` from `(1, 2)`; the CLI displays the synthesized program, while the
regression test also evaluates it. Returning the input does not satisfy this
specification.

The checked [relational_reverse.ae](../examples/synthesis/synquid/relational_reverse.ae)
implements the relational list from PLDI 2016 §2, Example 3. Each constructor
result retains `r`, and the tail has type `(RList {v:a | r head v}){|r|}`. Its
`snoc` helper and `reverse` implementation are checked polymorphically, including
termination, length preservation, and reversal of the relation:

```aeon
forall a:B, forall <r:a -> a -> Bool>,
(xs:(RList a){|r|}) ->
{ys:(RList a){|fun x => fun y => r y x|} | RList.size ys = RList.size xs}
```

Running that file evaluates the reversal of `[1, 2, 3]` to `[3, 2, 1]`. It includes
explicit refined type arguments on recursive calls and constructors: ordinary
elaboration does not infer all of these nested element refinements. This is a
checked implementation, not a claim that the entire recursive body is synthesized
within a short budget. The
[List-Reverse.ae](../examples/benchmarks/synquid/List-Reverse.ae) benchmark now
uses that relation and rejects the identity function. Both versions still omit
the upstream element-set preservation clause. The
[benchmark audit](../examples/benchmarks/synquid/README.md) records this gap and
compares all 64 ports against pinned original sources. It also restores the
indexed predicate in `List-Ith` and the dependent relation in `List-Foldr`.

Multiple predicate arguments use repeated brackets, for example
`Triple{|r|}{|s|}`. Predicates may have more than two arguments, provided every
domain is a first-order logical sort and the result is `Bool`. Constructor
results must retain all declared predicates in declaration order. Implicit
predicate inference uses the existing finite qualifier vocabulary; supply an
explicit lambda when the desired relation is outside that vocabulary.

## Incremental constraints

`ConstraintState` owns the typing/path context, precise contextual witnesses,
subtype obligations, type assignments, predicate vocabularies, and alternative
liquid assignments. `fork()` copies mutable assignments. Sibling alternatives and
opposite paths cannot inherit each other's mutations. Term memoization remains
disabled because `(context, level, goal)` does not identify pending constraints.

`ApplicationState` implements APPFO/APPHO. Required result shapes constrain
polymorphic instantiations while fresh predicates retain their refinements.
Result obligations mentioning an unchosen formal remain pending. An argument
contributes its inference VC and precise type; existential binders are opened
into the branch context. Variables and literals substitute into dependent
parameters, while compound expressions use contextual witnesses. Higher-order
arguments can be delayed until first-order arguments determine their requirements.

Incremental unification follows Fig. 6. Free/free subtype pairs remain related
without identifying their refinements. Unifying a free variable with a structured
type creates fresh nested variables and predicates. Outer refinement constraints
can be solved while element shapes remain unknown. Later arguments resolve those
shapes; an occurs check rejects infinite types. Unanchored shapes come from
component signatures and nested argument applications. Residual unconstrained
variables are closed at complete elimination terms, and their pending constraints
are checked before emission.

Type consistency uses the same VC lifting and SMT translation as verification,
including datatype measures and path assumptions. A prefix of length six cannot
produce an append result of length five with a nonnegative suffix: search rejects
that partial application before opening the suffix generator. Consistency is
existential and necessary; it does not approve a completed program.

## MUSFIX and qualifiers

The synthesis-specific Horn solver starts predicates at `true` and strengthens
negative occurrences. `verification/horn.py` retains its verification-oriented
algorithm. Strengthening uses an incremental SMT solver with tracked qualifier
assumptions and a fixed negated Horn head. Unsat cores seed MUS minimization;
a MARCO Boolean map blocks supersets of MUSes and subsets of maximal satisfiable
sets. Predicate-tagged selectors preserve alternative partitions of a MUS among
unknowns. Following §3.6, semantic minimization compares the valuations produced
by MUS enumeration, including implications between whole conjunctions. There is
no eager all-pairs implication ordering of the input qualifiers. Incomparable
alternatives remain available to subsequent constraints.

Qualifiers are sorted templates harvested from the specification and component
types, instantiated over visible variables. They include Boolean predicates and
datatype measures as well as integer relations. Neither qualifier count nor
conjunction width has a synthesis-specific cap. The solver has no default
256-query/valuation limit; SMT queries use the remaining synthesis deadline.
Unknown or unsupported results cannot certify a completed candidate. Partial
applications may defer obligations until their arguments are known, but completed
applications, leaves, and matches must discharge their construction proofs.
Failure to certify a candidate is not a proof that no program exists.

## Bounds and compatibility

The existing 4,000-candidate cap per application level and 64 proposed branches
per abduction search remain unchanged. `synquid_max_level`,
`synquid_max_candidates`, and the overall time budget can further bound a run.
The older `size_merge` and `iterative_deepening` ordering modes remain available.

This is an implementation of the paper's rules in Aeon, not a bit-for-bit port
of the original tool. The component library, qualifier language, datatype
lowering, SMT theories, and final verifier are Aeon's. The paper's formal
completeness theorem is not a guarantee for a capped or timed run, or for
obligations outside Aeon's supported logic. Full original benchmark coverage
and performance parity are not claimed.

## Reproducible validation

```bash
python -m pytest tests/synquid*test.py tests/smt*test.py tests/termination*test.py
python scripts/bench_synquid_round_trip.py
python scripts/run_core_tests.py
pre-commit run --all-files
python -m aeon --budget 15 -s synquid --no-main examples/benchmarks/synquid/List-Null.ae
python -m aeon --budget 25 -s synquid --no-main examples/benchmarks/synquid/List-Append.ae
```

The counter script fixes a finite grammar with one prefix and eight nonnegative
suffix lengths. Run the same script against baseline `5a0821b9` by setting
`PYTHONPATH` to a checkout of that commit.

| Fixture / revision | Argument candidates | Suffix generators | Partial rejections | Complete local rejections | Full validations | Verified solutions |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Prefix length 6 / baseline | 9 | 1 | 0 | 0 | 8 | 0 |
| Prefix length 6 / round-trip | 1 | 0 | 1 | 0 | 0 | 0 |
| Prefix length 3 / baseline | 9 | 1 | 0 | 0 | 8 | 1 |
| Prefix length 3 / round-trip | 9 | 1 | 0 | 7 | 1 | 1 |

These counts measure early pruning, not wall-clock speed. Tests cover exhaustive
finite-grammar solution preservation, branch isolation, weakest guards,
SMT unknowns, incremental shape/refinement discovery, polymorphic identity,
conditional nesting, synthesized predicate wrappers, matches on applications,
and generated measured recursion. Match regressions also cover opaque element
predicates, computed scrutinees, nested refined type arguments, binary predicates,
and rejection of invented explicit or implicit field invariants.
Accepted fixtures pass the final verifier;
non-decreasing monomorphic and explicitly type-applied polymorphic calls fail it.
The SMT regressions also check that polymorphic datatype measure specializations
use their actual carrier sort and reject an incorrect result.

The then-current `List-Null` and `List-Append` benchmark specifications were also
run during the round-trip implementation. The subsequent
[benchmark audit](../examples/benchmarks/synquid/README.md) replaces their broad
standard-library imports with the original local datatype/component setup.
Results from the older grammar should not be compared as if it were unchanged.
