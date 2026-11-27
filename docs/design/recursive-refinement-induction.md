# Recursive reflection and induction

Status: implemented. This supersedes the earlier scope decision for
[issue #328](https://github.com/alcides/aeon/issues/328).

## Definition equations and induction are separate

A terminating recursive function can be reflected without automatically proving
inductive properties of it. Aeon uses a LiquidHaskell-style division of work:

1. Check the body and its declared refinements using a termination-gated recursive
   hypothesis.
2. Prove strict lexicographic decrease and non-negativity of the termination
   metric independently of the function's own reflection and postcondition.
3. Expose defining equations at relevant call sites through bounded, path-sensitive
   Proof by Logical Evaluation (PLE).
4. Check inductive theorems through explicit `induction`, which elaborates into
   terminating recursive proof functions.

No universally quantified recursive axioms are added to SMT.

## The `_` marker

Simple non-recursive bodies still expand `_` directly into `result = body`.
Recursive and structured bodies instead expose `result = f(arguments)` in their
return refinement. `ReflectedFunctionDeclaration` carries the checked core body
and its formal parameters separately. The core extractor translates exhaustive
inductive eliminators into guarded expressions using SMT datatype recognizers
and selectors. Pure local values are inlined; native functions, higher-order
bodies and local recursive functions remain outside the reflection fragment.
The extended datatype/helper extraction requires the reflected result identity
`r = f(arguments)`, preserving the opacity of ordinary unmarked definitions and
manually stated recurrences. A termination metric alone does not request it.

Recursive reflection requires a termination metric. Unary integer definitions
may infer `[argument]`; other definitions use explicit `decreasing_by [...]`.
The presence of a metric enables conditional reasoning, but acceptance also
requires proving the independent termination obligations. Invalid metrics cannot
be justified using inconsistent self-reflection.

## Path-sensitive call instantiation

`aeon/verification/reflection.py` adds ground equations to each SMT leaf. It
checks the reflected function's input preconditions and decides each conditional
or constructor guard using the current premises. An undecided branch stays
opaque; a symbolic `cons x tail` is precise enough to unfold one step even when
`tail` is unknown. Equations retain call identities so congruence and induction
hypotheses such as `size (reverse tail) = size tail` remain applicable.

Argument substitution is simultaneous. Polymorphic functions and constructors
are specialized at each call's carrier types, including selector results.
Equations never apply outside the function's checked input domain. During body
checking, the reflected signature retains input preconditions but erases the
unproved return postcondition.

Evaluation is bounded by 256 equations, 256 worklist rounds, and a per-expansion
limit of 4096 nodes / depth 96. Guard queries have a bounded SMT timeout. A bound
or unknown guard merely stops unfolding; it never establishes the goal.

## Example: length of reverse

The reflected reverse equation exposes `append (reverse tail) [x]` in a `cons`
case. `List.append` has a checked length contract and decreasing size metric.
The `induction xs` hypothesis supplies the length of `reverse tail`; arithmetic
then proves the recursive case. Reflection supplies the defining equation,
while induction supplies the smaller-input theorem.

Executable examples live in `examples/syntax/recursive_reflection.ae`.
Soundness and regression coverage lives in `tests/recursive_reflection_test.py`,
`tests/reflect_underscore_test.py`, and `tests/recursion_soundness_test.py`.
