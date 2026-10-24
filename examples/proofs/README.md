# Checked equational proofs

This port follows Vazou et al., [*Theorem Proving for All: Equational Reasoning
in Liquid Haskell*](https://goto.ucsd.edu/~nvazou/theorem-proving-for-all/main.pdf)
(Haskell Symposium, 2018) and its
[companion source](https://github.com/nikivazou/EquationalReasoningInLiquidHaskell)
at revision `e79da2ef5f258048dd581376d559c2d92fe44273`.
Adapted source is covered by the upstream MIT license in `UPSTREAM-LICENSE`.
`manifest.json` inventories the paper, literate chapters, standalone modules,
and historical variants. Repeated presentations of the same theorem share a port.

```aeon
theorem add_commutative (a:Int) (b:Int) : a + b = b + a := by
  smt

theorem add_zero (x:Int) : x + 0 = x := by
  calc
    x + 0 = 0 + x := by exact add_commutative x 0
    _ = x := by smt
```

`theorem name ... : P := proof` elaborates to a checked Unit-valued definition
with refinement `P`. No proof-combinator import is required. Every theorem must
be complete during compilation, including `--check`: explicit holes, omitted
match branches, and tactic scripts that leave goals are compilation errors.
Ordinary definitions retain their existing synthesis-hole behavior.

Proof blocks support indentation or explicit parentheses and semicolons:

- `smt` asks the refinement checker to discharge the current proposition.
- `exact term` checks the supplied proof against the current proposition.
- `have h : P := by ...` checks an intermediate proposition and makes its proof
  available to subsequent steps.
- `calc` checks each equality and the connection between adjacent steps. `_`
  means the previous right-hand side.
- `cases x with | constructor fields => ...` checks constructor branches.
- `induction xs with | nil => smt | cons x tail ih => simp [ih]` introduces
  checked recursive proofs on constructor fields. Induction hypotheses follow
  the constructor's fields in declaration order. Standard `List` induction uses
  `List.structuralRank`; other datatypes require `decreasing_by [...]`.
- `simp [facts]` and `rw [facts]` make checked lemma applications available to
  the SMT checker, which uses equality congruence and existing function
  equations. `rw [facts]; ...` retains the facts for subsequent steps. These
  tactics use Aeon's existing reflection/contracts; they do not implement
  Lean's simplifier attributes, rewrite orientation, or arbitrary match unfolding.
- Existing synthesis tactics such as `assumption` and `apply?` can appear in a
  theorem's `by` block. They run during compilation and their output is checked.
  Whether synthesis is used depends on the tactic, not on `theorem` itself.

Calls inside refinement predicates must satisfy their preconditions before
compile-time evaluation. A parameter refinement that is `false` (including a
closed predicate that evaluates to `false`) produces a warning, not an error.
A Boolean parameter constrained to equal the Boolean value `false` is inhabited
and does not trigger that warning.

The previous `ProofCombinators` library and its operators remain available for
compatibility. The positive paper examples use theorem declarations and `calc`.

## Examples

`Arithmetic.ae` contains integer commutativity and chained/explained equalities.
`Induction.ae` is a standalone append-right-identity proof over standard `List`.
`Paper.ae` covers all substantive proof examples from sections 2–5: list lengths,
singleton reversal, identity, associativity, reversal distributivity and
involution, accumulator reverse, tree flattening, code sequencing, naive compiler
correctness, the optimized compiler, equivalence, and its independent direct
correctness proof. Section 6's Coq/Isabelle comparisons state the same append
associativity theorem, already represented by `assocP`.

The initial specification and case-split derivations are retained as
`reverseApp0`, `reverseApp1`, and `flattenApp0`. Names ending in `Fast` replace
Haskell names ending in an apostrophe. The historical addition-count invariant
is included in the compiler contracts, with executable `exprAdds` and `addCount`.

Run from the repository root:

```sh
python -m aeon examples/proofs/Arithmetic.ae --no-main --check
python -m aeon examples/proofs/Paper.ae
pytest -q tests/proof_combinators_test.py
```

The executable example returns 42 after exercising reversal, flattening, both
compilers, and underflow on zero- and one-element stacks. Tests also require
rejection of false equality, false theorem conclusions, circular contracts,
non-decreasing recursion, an incorrect machine, and a missing induction
hypothesis. Runtime examples complement the universal refinement proofs.

## Adaptations and boundaries

- The paper's list theorems use the standard `List Int` datatype; the compatibility
  combinator library itself remains polymorphic. The tree and compiler already use integers.
- `Code` fuses `[Op]` into `done`, `PUSH n rest`, and `ADD rest`. `app` is its
  concatenation. Results use standard `Maybe (List Int)`, preserving failure on underflow.
  `bindExec` requires successful results to carry a list of nonnegative structural
  rank; `exec` guarantees this invariant. This makes its calls satisfy their
  preconditions in both executable code and refinement specifications.
  `bindExec` specializes monadic bind to the continuation `exec d`; it does not
  claim a general higher-order reflection facility.
- The reference `append`, `reverse`, and `length` definitions retain the paper's
  algorithms and checked equations, operating on standard library lists.
  Constructor calls explicitly select the unrestricted element predicate
  (`{|fun value => true|}`), avoiding repeated abstract-refinement inference.
- Aeon does not yet reflect arbitrary pattern matches automatically. Function
  signatures give guarded defining equations, and the checker verifies those
  equations against every implementation branch. There are no trusted proof
  axioms, native proof helpers, or assumed theorem bodies in these examples.
- Recursion uses explicit `decreasing_by` metrics. The examples use `List.structuralRank` for lists and `rank` for domain datatypes,
  leaving it as a constructor-constrained logical measure rather than eagerly
  expanding a recursive SMT size function. Constructor equalities and
  refinements provide induction cases; calls on smaller arguments supply the
  induction hypothesis. Intermediate calls expose defining equations to the SMT
  solver, rather than claiming LiquidHaskell's full PLE automation.
- Aeon evaluates arguments eagerly. Equational steps and explanations may run;
  the paper's Haskell-specific proof-erasure/identical-Core inspection result is
  **not** claimed. `Fast` describes the accumulator algorithm, not a benchmark
  or a guarantee that proof work has been erased.
- Ordinary `def` declarations treat omitted match branches as synthesis holes.
  `negative/incomplete.ae` preserves this compatibility example. The same missing
  branch in a `theorem` is a compilation error.
  The tests require successful checking **and no remaining holes** for every
  positive port. Merely parsing a file or using `qed` does not certify totality.
- Native functions and user-declared axioms retain their existing trust
  semantics. Tactic-generated proof terms are rechecked. Theorem syntax uses
  Aeon's refinement checker; it does not add a standalone proof kernel.
