# Ninety-Nine Problems in Aeon

This directory contains Aeon solutions to a subset of the classic
[Ninety-Nine Lisp Problems](https://www.ic.unicamp.br/~meidanis/courses/mc336/2009s2/prolog/problemas/)
(also adapted for Lean as
[Lean99](https://lean-ja.github.io/lean99/)).  They serve as a small
showcase of how expressive Aeon is — and in particular how its
**Liquid (refinement) types** let us encode safety properties directly
in function signatures.

This addresses [issue #56](https://github.com/alcides/aeon/issues/56).

## Coverage

| Range       | Topic                       | Notes                                            |
| ----------- | --------------------------- | ------------------------------------------------ |
| 1–10        | Basic list operations       | last, kth, reverse, palindrome, flatten, …       |
| 11–13       | Run-length encoding         | direct, modified and decode variants             |
| 14–21       | List transforms             | duplicate, replicate, drop, split, slice, rotate |
| 22–26       | Ranges & random selection   | range, random sample, lotto, permutation, combos |
| 31–34       | Number theory predicates    | primality, gcd, coprime, Euler totient           |
| 35–36       | Prime factorization         | flat and multiplicity forms (uses `sympy`)       |
| 39–41       | Primes & Goldbach           | prime ranges, Goldbach decomposition             |
| 46, 49      | Logic & codes               | truth tables, Gray codes                         |
| 55–56       | Binary trees                | inductive type + recursive predicates            |

## Highlights of Aeon expressiveness

Several problems use refinement types to encode preconditions and
post-conditions that would have to be runtime checks or comments in
mainstream languages:

* `p01_last.ae` — the input list must be non-empty
  (`{x:(List a) | List.size x > 0}`)
* `p03_kth.ae` — the index must be in range
  (`{n:Int | n >= 0 && n < List.size l}`)
* `p04_length.ae` — the return value is provably equal to the list size
  (`{n:Int | n = List.size l}`)
* `p05_reverse.ae` — the result has the same size as the input
* `p14_duplicate.ae`, `p15_replicate.ae` — the output size is exactly
  `n * size l`
* `p17_split.ae`, `p18_slice.ae`, `p20_remove_at.ae`, `p21_insert_at.ae`
  — valid index range and exact output size
* `p32_gcd.ae` — recursive gcd with a `decreasing_by` clause for
  termination
* `p55_balanced_tree.ae`, `p56_symmetric_tree.ae` — user-defined
  inductive `Tree` / `BTree` types with structurally-recursive predicates

## Running

```bash
uv run python -m aeon examples/99problems/p01_last.ae
```

The CI smoke-test script `run_examples.sh` exercises the whole folder
via the `--no-main --budget 10` mode used for the rest of the example
suite.

## Notes / limitations

* Aeon's primitive `List` is monomorphic at runtime — the parametric
  refinement `List a` is only fully exploited in some examples; in
  others we use `List Int` directly to keep the type checker happy.
* Several problems delegate to a single Python expression via `native`
  (e.g. `p10_encode.ae` uses `itertools.groupby`).  This is in the
  spirit of Aeon's Python FFI: the *types* are still checked by Aeon,
  including refinements, while the implementation reuses Python.

## Mapping to the original 99 problems

```
1-Last          11-EncodeMod   21-InsertAt    33-Coprime      46-TruthTable
2-SecondLast    12-Decode      22-Range       34-Totient      49-GrayCode
3-Kth           13-EncodeDir   23-RndSelect   35-PrimeFactors 55-Balanced
4-Length        14-Duplicate   24-Lotto       36-PrimeFactMul 56-Symmetric
5-Reverse       15-Replicate   25-RndPerm     39-PrimesRange
6-Palindrome    16-DropEvery   26-Combine     40-Goldbach
7-Flatten       17-Split       31-IsPrime     41-GoldbachList
8-Compress      18-Slice       32-Gcd
9-Pack          19-Rotate
10-Encode       20-RemoveAt
```
