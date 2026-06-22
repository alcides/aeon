# Contata benchmarks — faithful aeon transcription

This directory transcribes the benchmark suite of **Contata** (Miltner, Wang,
Chaudhuri & Dillig, *Relational Synthesis of Recursive Programs via Constraint
Annotated Tree Automata*, CAV 2024) — the paper behind aeon's `cata`/`contata`
backends.

## Where the benchmarks come from

The suite is **not** in the paper PDF; it lives only in the public artifact:

> **https://github.com/amiltner/ContataArtifactEvaluation** — `benchmarks/`

It holds exactly **30** `.mls` files in four categories (Table 1; Contata solves
22/30, the baseline 8/30):

| Category | Dir in artifact | Count |
| --- | --- | --- |
| MR  — Mutual Recursion          | `mutrec/`        | 7  |
| RC  — Recursive Comparators     | `reccomp/`       | 7  |
| PDS — Partial Data Structures   | `ds/`            | 12 |
| SO  — Stack Overflow (k-safety) | `stackoverflow/` | 4  |

A `.mls` states `synth f : T calling [g,…]` (names the callable functions,
including the self/mutual partner — the recursion mechanism), a `satisfying`
block of helpers, and a spec of `test forall …` properties and `io … -> …`
examples.

## Two backends on master, and what each needs

- **`-s contata`** — the *genuine paper algorithm*: a constraint-annotated tree
  automaton whose alphabet includes the functions under synthesis as
  **uninterpreted functions**, accepted under a z3 model against the `@example`
  facts, with well-foundedness and MinTree extraction. It really does synthesise
  recursive and **mutually-recursive** definitions from examples — e.g. master's
  [`../mutual_pbe.ae`](../mutual_pbe.ae) recovers
  `even x = if x = 0 then true else odd (x-1)` and its dual. Its value domain is
  bounded (Int/Bool, plus `List Int` destructors), so it covers the MR flagship,
  integer comparators, and list-fold PDS — not arbitrary user datatypes.
- **`-s cata`** — the enumerate-and-typecheck approximation: discharges a
  *refinement-type* spec with the liquid typechecker. Solves only shallow integer
  relational holes (`v = x + x` → `x + x`).

Two language facts (verified on master `67bc6eae` while building this dir) shape
the transcription:

1. **Mutual recursion IS expressible** (issue #397): a Lean-style `mutual … end`
   block co-binds and co-typechecks the group, with a shared well-founded
   metric. `even_odd.ae` below uses it directly.
2. **`match` is NOT path-sensitive.** In `| .succ m => …` the checker does not
   learn `n = succ m`, so a relational *refinement* over a user ADT fails to
   typecheck **even on the ground-truth body**. This is why the richer-datatype
   benchmarks here are specified by `@property`/`@example` (PBT), not by a
   refinement-type hole — mirroring Contata's own `test forall … ` + `io` specs.

## What is here

Faithful transcriptions over the **original datatype shapes** (`nat`↦`Int`,
plus `inductive` list/tree), each = the datatype + helpers + the **reference
solution** + Contata's spec as `@property(N)`/`@example`. All verified with
`uv run python -m aeon --test <file>` (master):

| File | Contata source | Category | Spec checked | Status |
| --- | --- | --- | --- | --- |
| [`mutrec/even_odd.ae`](mutrec/even_odd.ae) | `even_odd.mls` | MR | `is_odd(inc x)=is_even x`; alternation | true `mutual` group ✔ |
| [`mutrec/evens_odds.ae`](mutrec/evens_odds.ae) | `evens_odds.mls` | MR | length-partition; unfolding eqn + IO | true `mutual` group ✔ |
| [`reccomp/list_eq.ae`](reccomp/list_eq.ae) | `list_eq.mls` | RC | reflexivity; singleton-diff; length-mismatch + 3 IO | ✔ |
| [`reccomp/binary_tree_depth.ae`](reccomp/binary_tree_depth.ae) | `binary_tree_depth.mls` | RC | node unfolding; deeper-than-children + 2 IO | ✔ |
| [`ds/mirror_tree.ae`](ds/mirror_tree.ae) | `mirror_tree_test.mls` | PDS | involutivity `mirror∘mirror=id`; subtree swap | ✔ |
| [`ds/list_insertion.ae`](ds/list_insertion.ae) | `list_insertion.mls` | PDS | membership added; sortedness preserved + IO | ✔ |
| [`stackoverflow/list_rev_twice.ae`](stackoverflow/list_rev_twice.ae) | `list_rev_twice.mls` | SO | k-safety `reverse∘reverse=id` + IO | ✔ |

Run all:

```bash
for f in examples/synthesis/cata/contata/**/*.ae; do uv run python -m aeon --test "$f"; done
```

These seven span all four categories; the remaining 23 follow the same recipe
(their datatypes and properties are in the artifact above).

## Honest status vs. the paper

- **Specs: faithful.** Each file checks the same properties/examples the source
  `.mls` states, over the same datatype shapes.
- **Mutual recursion: now first-class** (`mutual … end`), and **`-s contata`
  solves the MR flagship even/odd and integer/list-fold cases from `@example`s**
  — the paper's algorithm, reproduced. See [`../mutual_pbe.ae`](../mutual_pbe.ae)
  and [`../contata_pbe.ae`](../contata_pbe.ae).
- **Not yet solved by synthesis:** benchmarks over *user-defined* tree/list ADTs
  (depth, mirror, sorted-insert, list-eq over `inductive` types) lie outside
  `contata`'s bounded Int/Bool/`List Int` value domain; and they cannot be posed
  as `cata` refinement holes because `match` is not path-sensitive. These files
  therefore ship as **checked reference solutions + faithful specs**, the bridge
  a future ADT-aware `contata` domain (or path-sensitive `match`) would close.
