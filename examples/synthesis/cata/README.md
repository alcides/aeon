# CATA benchmarks (Constraint-Annotated Tree Automata)

The `cata` backend implements the line of Miltner, Wang, Chaudhuri & Dillig,
*Relational Synthesis of Recursive Programs via Constraint Annotated Tree
Automata* (tool **Contata**). It synthesizes a function from a **relational
refinement** spec (a refinement relating the parameters to the result),
discharging each candidate with the liquid typechecker as the constraint oracle.

```bash
uv run python -m aeon --no-main -s cata --budget 30 examples/synthesis/cata/<file>.ae
```

## The paper's benchmark suite vs. what is here

The paper evaluates Contata on **30 benchmarks** in four categories (Table 1):

| Category | Count | Paper example | In aeon? |
| --- | --- | --- | --- |
| Mutual recursion (MR) | 7 | even/odd (`evens`/`odds`) | ◐ co-synthesis of `mutual` holes |
| Recursive comparators (RC) | 7 | int-tuple list equality | ◐ relational subset |
| Partial data structures (PDS) | 12 | binary-tree removal | ◐ partial |
| Stack Overflow (SO) | 4 | reverse a list twice | ◐ `@property` k-safety oracle |

The benchmarks are **not individually published** in the paper (only category
counts plus one example each; sourced from Stack Overflow, FP textbooks, and
verification benchmarks), and no artifact repository is linked.

**What aeon's CATA backend can express, and what it cannot.** aeon's `cata`
synthesizes a function from a *refinement-type* spec. Each hole is solved one at
a time and discharged by the liquid typechecker.

- **Mutual recursion** (MR) — *partially supported*. A Lean-style
  `mutual ... end` block (see `aeon/sugar/aeon_sugar.lark`) makes each member a
  top-level binding, so all members become synthesis targets, and the
  `companions` machinery keeps the *siblings* in scope while each hole is solved.
  A candidate for one member may therefore call another; the sibling's declared
  refined type over-approximates its (co-synthesised) behaviour — the
  refinement-typed reading of CATA's constraint-annotation acceptance. See
  `mutual_cosynth.ae`. What remains: simultaneous example-driven (PBE) filling,
  where evaluating one member's `@example` requires the sibling to already be
  filled — true co-search rather than sibling-as-typed-oracle.
- **Relational / k-safety specs** relating *multiple* functions or multiple runs
  of one function (much of RC and all of SO, e.g. `f (f x) = x`) — expressible as
  a `@property`, which is both (a) a co-synthesis acceptance oracle, checked
  under property-based testing alongside the per-function refinement types and
  `@example`s, and (b) a **counterexample-driven guide** (CEGIS): a failing
  property's input is run under the instrumented semantics, the property is
  encoded as a relational constraint, and z3's unsat core blames the conflicting
  calls while a model derives concrete per-function obligations — propagated down
  the call chain to the example-anchored base cases. See `relational_property.ae`.

So the single-function files here are a **feasible reconstruction** in the spirit
of the RC category: functions whose *relational refinement* (parameters ↔
result) pins down the implementation, which aeon's CATA discharges via the liquid
typechecker. `mutual_cosynth.ae` exercises MR co-synthesis, and
`relational_property.ae` a k-safety property over a mutual group.

## `-s contata` — the paper-faithful version space

The `cata` backend above *discharges* a refinement-type spec one candidate at a
time. The `contata` backend is the paper's actual **version space** (the CATA of
the title): a candidate body denotes **symbolically** as a z3 expression over the
functions under synthesis treated as *uninterpreted functions* (the constraint
annotation), and is **accepted under a model** (Def. 6) iff the ground `@example`
specification together with the body's denotation at every example input is
satisfiable — one SMT query. Recursion and mutual recursion need no fixpoint
(the calls are uninterpreted), the well-foundedness side condition `v' ≺ v_in`
(Fig. 5) rejects non-terminating bodies, and the **smallest** accepted tree is
returned (MinTree, Def. 11). Observationally-equivalent member-call-free
sub-programs are merged by their value-vector (FTA-style compression).

```bash
uv run python -m aeon --no-main -s contata examples/synthesis/cata/contata_pbe.ae
```

The version space genuinely synthesises the paper's flagships from examples:

- **MR** — `even`/`odd` co-synthesised from `@example` facts, each body a
  base/recursive conditional that calls its *sibling* (the mutually-recursive
  solution, accepted jointly under one model).
- **PDS** — `length : List Int -> Int` recovered as
  `if isEmpty xs then 0 else 1 + length (tail xs)` from trace-closed examples;
  list values are opaque SMT constants, the `isEmpty`/`head`/`tail` destructors
  fold concretely, and the well-founded measure is list length.

See `tests/contata_test.py`. The single-hole `-s contata` CLI path covers the
Int/Bool fragment (it rebinds the version-space body onto the real in-scope
parameter, recursive self-call, and operators monomorphised at `Int`, then
discharges it through the typechecker); the richer mutual/list version space is
exercised through its API. Full benchmark-suite coverage (deeper integer
accumulators, trees) and property-driven CEGIS guidance remain future work.
