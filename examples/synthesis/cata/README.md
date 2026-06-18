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
| Mutual recursion (MR) | 7 | even/odd (`evens`/`odds`) | ✗ out of scope |
| Recursive comparators (RC) | 7 | int-tuple list equality | ◐ relational subset |
| Partial data structures (PDS) | 12 | binary-tree removal | ◐ partial |
| Stack Overflow (SO) | 4 | reverse a list twice | ✗ relational/k-safety |

The benchmarks are **not individually published** in the paper (only category
counts plus one example each; sourced from Stack Overflow, FP textbooks, and
verification benchmarks), and no artifact repository is linked.

**What aeon's CATA backend can express, and what it cannot.** aeon's `cata`
synthesizes a *single* function from a *refinement-type* spec. The paper's
defining features are out of scope here:

- **Mutual recursion** (MR) — co-synthesizing two functions (e.g. `evens` and
  `odds`) against a spec relating them — is not supported: aeon synthesizes one
  hole at a time.
- **Relational / k-safety specs** relating *multiple* functions or multiple runs
  of one function (much of RC and all of SO) cannot be stated as a single
  function's refinement.

So the files here are a **feasible reconstruction** in the spirit of the RC
category: single functions whose *relational refinement* (parameters ↔ result)
pins down the implementation, which aeon's CATA discharges via the liquid
typechecker. They exercise the backend's relational and conditional
(base/recursive-split) synthesis; the genuinely multi-function and
mutual-recursion benchmarks remain future work tied to extending the backend.
