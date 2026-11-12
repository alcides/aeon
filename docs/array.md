# `Array`: linear contiguous sequences

`Array.ae` is the standard library's flat, random-access sequence. Backing storage
is a Python `list`; refinements use the abstract `Array.size` measure. Since 4.9,
`Array` is a **linear type**: each owner must be consumed exactly once.
Read-only borrows may precede that consuming use.

- Source: [`aeon/libraries/Array.ae`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Array.ae)
- Generated reference: [stdlib/Array.html](stdlib/Array.html)

---

## Linearity in practice

Bind arrays at multiplicity **1**:

```aeon
let 1 xs := Array.mk_2 1 2 in
Array.consume Array.sum xs
```

Omitting `1` is a compile error. Consuming the same binder twice triggers
`LinearUsedTooManyTimesError`; dropping a linear value without consuming it
triggers `LinearUnusedError`.

| Pattern | API |
|---------|-----|
| Transform (consume → new array) | `mk_concat`, `set`, `reversed`, `map`, `filter` |
| Borrow (keep ownership) | `length`, `empty`, `get`, `head`, `sum`, `mean`, `count` |
| Move an element (consume array) | `take`, `take_head` |
| Fold and end ownership | `reduce`, `consume observer` |
| Release after the last borrow | `dispose` |
| Read element and keep array | `get_at` + `with_get` |
| Split into two independent arrays | `copy` → `with_pair` |

### Reading length before an update

`Array.length` and `Array.empty` borrow the array for the duration of the call.
The owner remains available for `Array.set` or another consuming operation:

```aeon
import Array;

def main (_:Int) : Int :=
    let 1 arr := #[5,9] in
    let n := Array.length arr in
    let 1 updated := Array.set arr (n - 1) 7 in
    Array.consume Array.sum updated;
```

This returns `12`. The length refinement proves the index is in bounds;
`set` preserves the size and element predicate. It consumes `arr`, so subsequent
reads must use `updated`. Aeon expresses updates by binding the array returned
by `set`; there is no assignment syntax.

Borrowing does not discharge the owner's linear obligation. If the last
operation is a borrowing read, explicitly release the array:

```aeon
let 1 arr := #[5,9] in
let n := Array.length arr in
let _ := Array.dispose arr in
n
```

User-defined readers declare `(borrow arr:(Array a))`. They can take more
arguments, including other borrows, and return scalars or independently owned
results. The borrowed handle itself cannot be returned, moved, or retained in
a closure. `get`, `head`, and `copy` require `[Copy a]`: primitive values and
immutable containers of copyable elements support this capability; arrays and
resource handles do not. `take` and `take_head` move nested linear elements.

Borrowing lasts through the **whole curried call**, including evaluation of
later arguments. `Array.get arr i` is supported; retaining `Array.get arr` in a
variable is rejected. A later argument also cannot consume `arr` while the
earlier borrow is active. Compute such arguments first, or keep the operation
inside a fully applied call. Inline callbacks accepted at multiplicity `1` may
consume captured owners once; reusable or escaping resource closures are rejected.

Native implementations are trusted to honor read-only access and independent
result storage, just as they are trusted to honor their refinement contracts.
Borrow qualifiers are part of function types and checked for callback arguments.

`set` updates the backing list in O(1), with ownership transferred to its result.
`copy` duplicates the outer buffer only after proving its elements are copyable,
so nested linear arrays cannot accidentally share mutable storage.

Length checks use `Array.length` directly. The length-wrapper API
(`len_of`, `len_value`, `len_array`, `with_len`, `ArrayLen`, and `held_size`)
has been removed. A length read can now be followed directly by a consuming
element read, as in [`examples/testing/array_tests.ae`](https://github.com/alcides/aeon/blob/master/examples/testing/array_tests.ae).

## Constructors

| Constructor | Result |
|-------------|--------|
| `mk_empty unit` | Fresh empty array; size 0 |
| `mk_repeat n v` | `n` copies of `v`; requires `n >= 0` |
| `mk_1`, `mk_2`, `mk_4`, `mk_8`, `mk_16`, `mk_32` | Exactly that many separately supplied elements, in argument order |
| `mk_concat xs ys` | Elements of `xs` followed by `ys`; size `size xs + size ys` |

Every constructor carries an exact size refinement. The fixed-arity constructors
and `mk_concat` preserve the element predicate and consume their inputs once.
`mk_repeat` takes an unrestricted value, with result type
`{xs:(Array {x:a | x = v}) | size xs = n}`; it cannot duplicate a linear handle.
Different arguments need not have different values.

```aeon
let 1 prefix := Array.mk_repeat 3 7 in
let 1 suffix := Array.mk_2 8 9 in
let 1 xs := Array.mk_concat prefix suffix in
Array.consume Array.sum xs  # 38
```

`mk_empty unit` is an applied action, so each evaluation creates a fresh buffer.
An empty literal `#[]` expands to that call. Nonempty literals use the largest
power-of-two chunks up to 32 elements, combined in a balanced `mk_concat` tree.
For example, `#[1, 2, 3]` expands to
`Array.mk_concat (Array.mk_2 1 2) (Array.mk_1 3)`.
Literals support arbitrary lengths and evaluate their elements left to right.

The old constructor names `new`, `append`, and `cons` have been removed.
To append one element use `mk_concat xs (mk_1 x)`; to prepend one use
`mk_concat (mk_1 x) xs`. The Boolean query `empty xs` tests whether an array
is empty.

---

## Element refinements

```aeon
linear type Array a forall <p : a -> Bool>
```

The type declares an abstract element predicate. Constructors express their
shared predicate as `a<p>` (shorthand for `{v:a | p v}`), so their result can be
used wherever an array with that element refinement is required. The measure
`size` threads through transforms so length proofs compose.

---

## Wrapper types

| Type | Purpose |
|------|---------|
| `ArrayPair a` | Two arrays from `copy` (consume together with `with_pair`) |
| `ArrayGet a` | Element + array from `get_at` |

Wrappers are linear: bind them with `let 1` and consume each exactly once.
The terminal projections (`fst_array`, `snd_array`, `got_value`, `got_array`)
consume the wrapper and discard its other field.
To recover both fields, use a continuation:

```aeon
let 1 read := Array.get_at #[5,9] 0 in
Array.with_get read (fun value => fun arr =>
    value + Array.consume Array.sum arr)
```

`Array.with_pair pair (fun left => fun right => ...)` exposes
both independent buffers returned by `copy`.

This replaces the old pattern of projecting the same wrapper twice. Repeated
array projections returned aliases to one buffer, allowing a native operation
that legitimately mutated its unique input to change another live reference.

---

## Interop

- **`Cuda.upload_*`** consumes a linear host `Array` and returns a `ReadyBuffer`.
- **`Database`**, **`Subprocess`**, and other modules use `Array` for argv lists
  and row materialization with ordinary refinements on top of linearity.
- **`DataFrame.col_as_array` / `with_col`** extract numeric columns as `Array Float`
  for `@llvm` / `@gpu` kernels (see [`dataframe.md`](dataframe.md)).

## LLVM / GPU kernels

Sized helpers (``ArrayKernels.ae``) (`map_n_int`, `reduce_n_int`, `count_n_int`, `zipWith_n_int`,
`map_n_float`, …) take an explicit length so the CPU/CUDA lowerers can emit
vector IR. Prefer unsized `map` / `filter` / `reduce` in ordinary Aeon code;
use `*_n*` only inside `@llvm` / `@gpu` functions.

```aeon
open Array
open ArrayKernels

@llvm
def add(acc:Int) (x:Int) : Int := acc + x;

@llvm
def sum_n (1 arr:(Array Int)) (n:Int) : Int :=
    reduce_n_int add 0 arr n;
```

`Array` is the single stdlib host-buffer name (the old `Vector.ae` library is
gone). Numpy LA types remain `Tensor.Vector` / `Tensor.Matrix`.

---

## Related reading

- [`DataFrame` + Array column bridge](dataframe.md)
- [`Cuda` GPU buffers](cuda.md)
- [State-safe `Database`](database.md)
- [Collection literals in the language guide](index.md#collection-literals)
