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

The **complete 30-benchmark suite**, over the **original datatype shapes**
(`nat`/`A`/`B` ↦ `Int`, plus `inductive` list/tree/forest/trie). Each file =
the datatype(s) + helpers + the **reference solution** + Contata's spec as
`@property(N)` (the `test forall …`) and `@example` (the `io …`). Unless noted
`(plain)`, each is verified with `uv run python -m aeon --test <file>`:

**MR — Mutual Recursion (7)**

| File | Source | Spec checked |
| --- | --- | --- |
| [`mutrec/even_odd.ae`](mutrec/even_odd.ae) | `even_odd.mls` | `is_odd(inc x)=is_even x`; alternation — true `mutual` group |
| [`mutrec/even_odd2.ae`](mutrec/even_odd2.ae) | `even_odd2.mls` | variant properties — true `mutual` group |
| [`mutrec/evens_odds.ae`](mutrec/evens_odds.ae) | `evens_odds.mls` | length-partition; unfolding eqn — true `mutual` group |
| [`mutrec/nested_list_eq.ae`](mutrec/nested_list_eq.ae) | `nested_list_eq.mls` | reflexivity; inner-diff; length-mismatch |
| [`mutrec/parenthesis_match.ae`](mutrec/parenthesis_match.ae) | `parenthesis_match.mls` | `is_open = not is_close` + 6 io |
| [`mutrec/tree_forest_size.ae`](mutrec/tree_forest_size.ae) | `tree_forest_size.mls` | mutual tree/forest size; growth props **(plain)** |
| [`mutrec/tree_forest_leaves.ae`](mutrec/tree_forest_leaves.ae) | `tree_forest_leaves.mls` | mutual tree/forest leaf count **(plain)** |

**RC — Recursive Comparators (7)**

| File | Source | Spec checked |
| --- | --- | --- |
| [`reccomp/list_eq.ae`](reccomp/list_eq.ae) | `list_eq.mls` | reflexivity; singleton-diff; length-mismatch + 3 io |
| [`reccomp/list_cmp.ae`](reccomp/list_cmp.ae) | `list_cmp.mls` | three-way (Eq/Lt/Gt) reflexivity; longer/shorter + io |
| [`reccomp/binary_tree_depth.ae`](reccomp/binary_tree_depth.ae) | `binary_tree_depth.mls` | node unfolding; deeper-than-children + 2 io |
| [`reccomp/binary_tree_eq.ae`](reccomp/binary_tree_eq.ae) | `binary_tree_eq.mls` | reflexivity; symmetry; proper-subtree + io |
| [`reccomp/ternary_tree_depth.ae`](reccomp/ternary_tree_depth.ae) | `ternary_tree_depth.mls` | depth unfolding (×3); `tt_cmp` reflexivity + io |
| [`reccomp/ternary_tree_eq.ae`](reccomp/ternary_tree_eq.ae) | `ternary_tree_eq.mls` | reflexivity; symmetry + io |
| [`reccomp/trie_eq.ae`](reccomp/trie_eq.ae) | `trie_eq.mls` | reflexivity; value-differs; subtrie; leaf-vs-node |

**PDS — Partial Data Structures (12)**

| File | Source | Spec checked |
| --- | --- | --- |
| [`ds/list_insertion.ae`](ds/list_insertion.ae) | `list_insertion.mls` | membership added; sortedness preserved + io |
| [`ds/list_insertion2.ae`](ds/list_insertion2.ae) | `list_insertion2.mls` | membership preserved (append-to-end) + io |
| [`ds/list_insertion3.ae`](ds/list_insertion3.ae) | `list_insertion3.mls` | no-new-elements (intended; see note) + io |
| [`ds/list_removal.ae`](ds/list_removal.ae) | `list_removal.mls` | removed element absent + io |
| [`ds/list_removal2.ae`](ds/list_removal2.ae) | `list_removal2.mls` | keeps exactly the others + io |
| [`ds/list_sort.ae`](ds/list_sort.ae) | `list_sort.mls` | ordered insert preserves sortedness + io |
| [`ds/bst_insertion.ae`](ds/bst_insertion.ae) | `bst_insertion.mls` | inserted found; existing preserved + io |
| [`ds/mirror_tree.ae`](ds/mirror_tree.ae) | `mirror_tree_test.mls` | involutivity `mirror∘mirror=id`; subtree swap |
| [`ds/mirror_tree_test2.ae`](ds/mirror_tree_test2.ae) | `mirror_tree_test2.mls` | period-2 group laws (binary, bool) + io |
| [`ds/mirror_ternary_test.ae`](ds/mirror_ternary_test.ae) | `mirror_ternary_test.mls` | involutivity (ternary, bool) + io |
| [`ds/mirror_ternary_test2.ae`](ds/mirror_ternary_test2.ae) | `mirror_ternary_test2.mls` | period-2 group laws (ternary) + io |
| [`ds/sized_list.ae`](ds/sized_list.ae) | `sized_list.mls` | size-cache invariant preserved + 2 io |

**SO — Stack Overflow / k-safety (4)**

| File | Source | Spec checked |
| --- | --- | --- |
| [`stackoverflow/list_rev_twice.ae`](stackoverflow/list_rev_twice.ae) | `list_rev_twice.mls` | k-safety `reverse∘reverse=id` + io |
| [`stackoverflow/pairs.ae`](stackoverflow/pairs.ae) | `pairs.mls` | even-length round-trip `flatten∘pairs=id` + io |
| [`stackoverflow/split_on.ae`](stackoverflow/split_on.ae) | `split_on.mls` | round-trip `concat∘split=id` + 2 io (exact shape) |
| [`stackoverflow/zip_same_len.ae`](stackoverflow/zip_same_len.ae) | `zip_same_len.mls` | `length(zip xs ys) = min(len xs, len ys)` + io |

Run them all (the two `(plain)` files via a plain run that prints `True`):

```bash
for f in examples/synthesis/cata/contata/**/*.ae; do
  case "$f" in
    *tree_forest_*) uv run python -m aeon "$f" ;;   # prints True
    *)              uv run python -m aeon --test "$f" ;;
  esac
done
```

### Two transcription notes

- **`tree_forest_{size,leaves}` use a plain run, not `--test`.** Their mutual
  group spans *two* datatype sorts (`Tree`, `Forest`); aeon's `--test` reflects
  called functions into z3, and reflecting a mutual group across distinct ADT
  sorts currently raises a z3 *“Sort mismatch”* (an aeon bug — the definitions
  themselves typecheck and run). So these verify by evaluating every io example
  and both properties in `main`, which prints `True`. (Single-sort mutual groups,
  e.g. `even_odd`, reflect fine.)
- **`list_insertion3`** transcribes the *intended* property (“insertion adds no
  element other than the one inserted”). The original `.mls` test, read
  literally, is contradicted by its own io, so the literal de-Morgan form is
  unsatisfiable; the file documents this.

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
