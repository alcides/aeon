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
import ProofCombinators;
def add_commutative (a:Int) (b:Int) : {p:Unit | a + b = b + a} :=
  a + b ==. b + a *** QED;
```

`ProofCombinators.eq` (`==.`) checks that its arguments are equal and returns
its **right** argument, as in the paper. `because` (`?`) accepts a Unit proof
and returns its left argument. `qed` (`*** QED`) discards the value and returns
Unit; the enclosing refined result type states the theorem. It does not assert
an unchecked proposition. `trivial` is Unit. Named `le`, `lt`, `ge`, and `gt`
combinators check integer inequalities and return their right argument.
The equality and explanation combinators are polymorphic.

Import `ProofCombinators` before using the notation. Arithmetic and Boolean
operators bind more tightly than proof operators. Explanation `?` binds more
tightly than left-associative `==.`; `*** QED` closes the chain. Parenthesize a
whole chain to attach a reason to it. A synthesis hole is written `?name`, with
no space; an explanation is written `value ? reason`. Use named functions when
passing combinators as values. `QED` is syntax here, rather than a runtime token.

## Examples

`Arithmetic.ae` contains integer commutativity and chained/explained equalities.
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

- The paper's list theorems are specialized to integer lists; the combinator
  library itself remains polymorphic. The tree and compiler already use integers.
- `Code` fuses `[Op]` into `done`, `PUSH n rest`, and `ADD rest`. `app` is its
  concatenation. `Result` is `Maybe Stack`, preserving failure on underflow.
  `bindExec` specializes monadic bind to the continuation `exec d`; it does not
  claim a general higher-order reflection facility.
- Aeon does not yet reflect arbitrary pattern matches automatically. Function
  signatures give guarded defining equations, and the checker verifies those
  equations against every implementation branch. There are no trusted proof
  axioms, native proof helpers, or assumed theorem bodies in these examples.
- Recursion uses explicit `decreasing_by` metrics. The examples call their structural measure `rank`,
  leaving it as a constructor-constrained logical measure rather than eagerly
  expanding a recursive SMT size function. Constructor equalities and
  refinements provide induction cases; calls on smaller arguments supply the
  induction hypothesis. Intermediate calls expose defining equations to the SMT
  solver, rather than claiming LiquidHaskell's full PLE automation.
- Aeon evaluates arguments eagerly. Equational steps and explanations may run;
  the paper's Haskell-specific proof-erasure/identical-Core inspection result is
  **not** claimed. `Fast` describes the accumulator algorithm, not a benchmark
  or a guarantee that proof work has been erased.
- Aeon treats omitted match branches as synthesis holes. `negative/incomplete.ae`
  reproduces the totality example: it must not count as a completed proof.
  The tests require successful checking **and no remaining holes** for every
  positive port. Merely parsing a file or using `qed` does not certify totality.
- Native functions, user-declared axioms, and synthesis are existing Aeon trust
  boundaries. This library is ordinary checked Aeon code, not a new standalone
  proof kernel.
