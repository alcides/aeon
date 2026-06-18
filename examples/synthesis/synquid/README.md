# Synquid benchmarks

Aeon ports of the synthesis suite from Polikarpova, Kuraj & Solar-Lezama,
*Program Synthesis from Polymorphic Refinement Types* (PLDI 2016) — the 64
`.sq` programs under
[`test/pldi16`](https://github.com/nadia-polikarpova/synquid/tree/master/test/pldi16)
of the Synquid tool. Each file states a datatype, a refinement-typed signature,
and a `?hole` for Aeon's synthesizer to fill:

```bash
# Attempt one benchmark (type-directed enumeration, 30s budget):
uv run python -m aeon --budget 30 -s synquid examples/synthesis/synquid/List-Reverse.ae

# Or with genetic programming:
uv run python -m aeon --budget 30 -s gp examples/synthesis/synquid/List-Replicate.ae
```

These are an *on-demand* suite (not swept by `run_examples.sh`): like the CSG and
Vericoding corpora, most are hard enough to exit "no solution found" inside a
short budget, so running all 64 on every push adds time without signal.

## Fidelity

The ports are faithful in structure; the remaining gaps to a 1:1 Synquid port
are being closed in order (see *Aligning further*). Current state:

1. **Polymorphism (done).** Element types are polymorphic (`forall a`,
   inferred from lowercase type variables) wherever the element is used only
   structurally — matching the Synquid originals. `Int` is retained only where
   the element is *ordered or integer-specific*:
   * `IncList-*`, `StrictIncList-*`, `BST-Sort` — the datatype carries an
     **order** invariant (`hd <= min(tail)`), which needs an order on the
     element; these go polymorphic once n-ary abstract refinements (#1) provide
     the order relation.
   * `UniqueList-Range` (enumerates an integer range) and `Evaluator` (an
     expression language over `Int` literals) are inherently integer.

2. **`Int`-measure invariants are encoded; richer invariants are documented.**
   * `List` length, `Tree`/heap node-count, AVL height — encoded exactly.
   * **Sortedness** is encoded *faithfully* for the sorted-list families: the
     `IncList` / `SList` datatypes carry the order invariant in their `cons`
     constructor (`hd <= min(tail)` / `hd < min(tail)`), so any value of that
     type *is* sorted.
   * **Two-sided / set / structural invariants** that Synquid expresses with
     *abstract refinements* — BST key ordering, binary-heap order, AVL balance,
     red-black colour/black-height, `elems`-set preservation, element
     uniqueness — are **not** yet encoded; those benchmarks are ported as
     structural (size/height) specs and flagged `Structural/size port` in the
     file. See *Aligning further*.

Datatypes with a standard-library equivalent use it directly (`List` via
`open List`, `Maybe` via `open Maybe`); only datatypes with **no** stdlib
counterpart are defined inline (`IncList`, `SList`, the polymorphic `Tree a`,
`BTree a`, `Heap a`, `Avl a`, `Rbt a`, the list-pair `LPair a`, `AddrBook a`,
and the monomorphic `Expr`).

> Using `open List` brings the whole List component library into the synthesis
> grammar — closer to Synquid's component-based setup. This relies on the
> `get_holes_info` fix in #344 (hole identification no longer crashes on
> hole-free polymorphic library bodies); before it, opening `List` next to a
> hole aborted synthesis.

## Coverage

All 64 parse, elaborate, and build the synthesis grammar without error
(verified with `aeon --no-main`; a handful are solved outright at a 3s budget).
Each file's top comment states its fidelity tier:

* **Exact** — size/length/height encoded precisely and, for the sorted-list
  families, the order invariant too.
* **Structural** — shape ported; a two-sided/set/colour/balance invariant
  documented as omitted (the `BST`, `BinHeap`, `AVL`, `RBT` families, the `List`
  sort variants, `List-Compress/Nub`, `UniqueList-*`).
* **Signature** — the result is deliberately unconstrained (`List-Elem`,
  `List-Ith`, `List-ElemIndex`, `List-Foldr`, `Tree-Elem`, `BST-Member`,
  `BinHeap-Member`, `Evaluator`).

By family: List (30), IncList (3), StrictIncList (3), Tree (4), BST (4),
BinHeap (5), AVL (6), RBT (3), AddressBook (2), Evaluator (1), UniqueList (3).

## Aligning further with the original

In order of planned work:

3. **Polymorphism — done** (above).
1. **N-ary abstract refinements over inductive datatypes** — the biggest lever.
   Synquid's BST order, heap order, and `IncList` bounds are datatypes
   parameterised by a relation, e.g. `data T a <r :: a -> a -> Bool>` (and, in
   general, *n*-ary relations, not only binary). Aeon already has unary
   abstract refinements on `List` (`forall <p : a -> Bool>`); generalising them
   to **n-ary** relations and to user trees lets BST/BinHeap/AVL/RBT and the
   sorted-list families carry their real invariants (and go polymorphic)
   instead of tracking only node-count.
2. **A `Set`/`elems` measure** for lists and trees, so `Elem`, `Delete`, `Nub`,
   `Compress`, `UniqueList-*`, and the sort benchmarks can state
   *element-set preservation* (and uniqueness) rather than only a length bound.
4. **Balance / colour invariants** (AVL balance, RBT colour & black-height),
   built on the n-ary refinements plus arithmetic over the height measure.
5. **Result-tying measures** for `List-Ith`/`ElemIndex`/`Foldr`/`Evaluator`.
6. **A `synquid` CI lane** (a curated subset that actually synthesizes), once
   the synthesizer solves them reliably, mirroring `PSB2/solved`.
