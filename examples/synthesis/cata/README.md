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
| Stack Overflow (SO) | 4 | reverse a list twice | ✗ relational/k-safety |

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
  of one function (much of RC and all of SO, e.g. `f (f x) = x`) still cannot be
  stated as a single function's refinement.

So the single-function files here are a **feasible reconstruction** in the spirit
of the RC category: functions whose *relational refinement* (parameters ↔
result) pins down the implementation, which aeon's CATA discharges via the liquid
typechecker. `mutual_cosynth.ae` additionally exercises MR co-synthesis. The
genuinely k-safety/relational multi-function benchmarks remain future work tied
to extending the backend.
