# Synquid PLDI16 benchmarks

This directory contains 64 Aeon ports of Polikarpova, Kuraj & Solar-Lezama's
*Program Synthesis from Polymorphic Refinement Types* suite. The review is pinned
to upstream commit
[`9bceb4cc775e07ab279fff8c51fdd86ae0b2878c`](https://github.com/nadia-polikarpova/synquid/tree/9bceb4cc775e07ab279fff8c51fdd86ae0b2878c/test/pldi16).
The original specifications are copied byte-for-byte into [upstream](upstream),
with their MIT [license](upstream/LICENSE). [manifest.json](manifest.json) records
the source checksum, original synthesis goals, fidelity and remaining differences
for **every** file. Tests check the inventory and checksums without network access.

**These are not all equivalent ports.** 25 files now preserve the original
target contracts and relevant datatype invariants, including `elems`
preservation on `List-Snoc` and `List-Reverse` and the strict child bound on
`BinHeap-Singleton`. The other 39 remain explicitly labelled legacy
approximations. A solution to one of those weaker problems must not be reported
as a solution to the upstream benchmark.

## Restored specifications

| Benchmarks | Original specification now expressed in Aeon |
| --- | --- |
| `List-Ith` | `p : Int -> a -> Bool`, `p 0 head`, index-shifted tail, bounded index, result satisfying `p i result` |
| `List-Foldr` | `p : List a -> b -> Bool`; the step receives the tail, element and related accumulator; the seed relates to nil and the result to the input |
| `List-Fold-Append`, `List-Fold-Length` | The original dependent `foldr` component, supplied as a checked Aeon definition |
| `List-Snoc`, `List-Reverse` | Persistent element relation, snoc's element bound, reversed predicate, and `elems` preservation |
| `UniqueList-Range` | Pairwise inequality, length `size`, elements in the **inclusive** interval `[lo, lo + size]`, arguments `size` then `lo` |
| `List-Concat` | Flatten `ListOfLists a` into `List a`, with length equal to `sumLen`; the old port was a cons operation |
| `List-Zip`, `List-Product` | Lists of pairs with two independent element types; zip requires equal input lengths and product has multiplicative length |
| `Tree-BalancedReplicate` | Equal child heights and requested output **height**, with arguments `x` then `h` |
| `BinHeap-Singleton` | Children strictly greater than the parent, key/left/right constructor order, and `elems` equal to the singleton set |
| `AddressBook-Make`, `AddressBook-Merge` | Original `Info`/`Address` records, privacy-based business/personal classification and total-size contracts |
| `Evaluator` | Translate `AST` to opcode-based `PAST` while preserving the result measure, including subtraction; the old port returned an unconstrained integer |
| `List-Append`, `List-Map`, `List-Null`, `List-Stutter`, `List-ZipWith`, `List-Replicate`, `List-Take`, `List-Drop`, `Tree-Count`, `Tree-ToList` | Preserve original contracts while restoring local datatypes and the declared helper components |

For example, the `ith` goal is now:

```aeon
def ith : forall a:B, forall <p:Int -> a -> Bool>,
    (xs:(List a){|p|}) -> (i:{v:Int | 0 <= v && v < List.len xs}) -> {v:a | p i v}
    decreasing_by [List.len xs] :=
    Λ a:B => Λ <p:Int -> a -> Bool> => fun xs => fun i => ?hole;
```

The datatype in [List-Ith.ae](List-Ith.ae) stores the predicate and shifts its
index in the tail. Returning the head regardless of `i` is rejected. Likewise,
[List-Reverse.ae](List-Reverse.ae) now rejects the identity function, and
[List-Foldr.ae](List-Foldr.ae) rejects returning the seed regardless of the input.
These checks use arbitrary abstract predicates, not a handful of examples.

The revised files declare their own datatypes rather than opening the entire
standard `List` library, which previously offered implementations of the very
operations being synthesized. Checked helper definitions are supplied only where
upstream declares those components. Constructor names use Aeon's lowercase,
qualified spelling; type-variable renaming is immaterial. Nonnegative measure
codomains and explicit termination metrics preserve the original inductive
hypotheses. The unused `elems` declarations in the fold and range examples are
omitted; none of their target/component contracts depend on them.

“Contract-faithful” in the manifest concerns the **logical problem**, not identical
search behavior: Aeon's prelude, automatic constructor machinery and qualifier
policy still differ from Synquid's. There is no claim of equal search grammars,
paper timings, or that a synthesizer solves every well-formed specification.

## Remaining differences

| Family | Remaining work |
| --- | --- |
| Set-based lists and trees | `List-Snoc` and `List-Reverse` now keep upstream `elems` preservation. BST, heap, AVL and red-black set contracts are still unrestored. Integer and Boolean sets stay native Z3 sets; other element sorts use macro-expanded membership. |
| `List-ElemIndex` | Restore indexed predicates **and** the membership precondition before replacing `Maybe Int` by the original dependent `Int` result. Dropping the precondition would make the problem unsatisfiable for absent elements. |
| `List-Compress`, `List-Nub`, `UniqueList-Insert/Delete` | Element-to-tail predicates and head/element set measures, rather than length bounds. These differ from the element-to-element relation used in `UniqueList-Range`. |
| `IncList-*`, `StrictIncList-*`, list sorting, `BST-*`, remaining `BinHeap-*` | Polymorphic refined element types, exact component signatures and set contracts. BST children have strict bounds. `BinHeap-Singleton` now has the strict child bound; insert, merge and tripleton do not. The old size approximations can mishandle duplicates. |
| `AVL-*` | Key bounds, balance, stored height field, balance factor, exact height contracts, set contracts and all rotation/merge goals. |
| `RBT-*` | Colors, red-child rule, equal black heights, `WeakRBT`'s `Ok`/`Bad` cases, set contracts and all intermediate goals. |

The new relation support makes several of these datatype invariants expressible.
`elems` on snoc and reverse is checked, and `BinHeap-Singleton` checks both the
strict child bound and the singleton set. The other BST, heap, AVL and
red-black set contracts are not. The manifest records per-file mismatches,
including changed argument/result types and missing goals. For example, upstream
`BST-Sort` has **five** goals, while its legacy Aeon file has only one. The legacy
files are retained for compatibility, with their former fidelity claims removed.

## Validation and running

```bash
# Compile all 64 and check restored contracts, including incorrect candidates:
uv run pytest tests/synquid_benchmark_test.py

# Attempt a benchmark without synthesizing a synthetic main function:
uv run python -m aeon --no-main --budget 30 -s synquid examples/benchmarks/synquid/List-Ith.ae
```

The suite is on demand and is not included in `run_examples.sh`. The regression
tests verify provenance, all 64 files' compilation, and original goal names in
the 25 revised files. Checked witnesses exercise dependent fold execution,
indexed-list predicates, reversal, uniqueness, balanced trees, the heap child
bound, address privacy and AST semantics; invalid witnesses must fail.

Two shared verification fixes were needed by the upstream contracts:

- Termination VCs now bind the function's abstract predicates, including when the
  implementation alpha-renames them. This matters for `foldr`'s refined seed.
- Structural SMT measures are installed only when constructor equations actually
  match structural cardinality, not because the measure is named `size` or `len`.
  The original evaluator uses leaf size one and binary-node increment two. A
  guessed zero/one measure contradicted those equations and accepted wrong code.
  Nonstructural measures retain their declared constructor facts.

A single five-second Synquid smoke attempt on each of the 24 files from that
review solved `List-Null` (0.221s including compilation); the other 23 exhausted
the search budget without a complete solution. `BinHeap-Singleton` was restored
later and was not part of that smoke. There were no crashes or process timeouts.
The [per-file results](validation.json) include source checksums and timings.
This is a smoke run, not a success-rate estimate or a comparison to the paper.
The solved program was checked again as a whole; the manually checked witnesses
in the tests are reported separately from synthesis successes.
