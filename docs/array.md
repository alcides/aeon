# `Array`: linear contiguous sequences

`Array.ae` is the standard library's flat, random-access sequence. Backing storage
is a Python `list`; refinements use the abstract `Array.size` measure. Since 4.9,
`Array` is a **linear type**: each value must be used exactly once.

- Source: [`aeon/libraries/Array.ae`](https://github.com/alcides/aeon/blob/master/aeon/libraries/Array.ae)
- Generated reference: [stdlib/Array.html](stdlib/Array.html)

---

## Linearity in practice

Bind arrays at multiplicity **1**:

```aeon
let 1 xs := Array.append (Array.append (Array.new{Int} unit) 1) 2 in
Array.sum xs
```

Omitting `1` is a compile error. Using the same binder twice triggers
`LinearUsedTooManyTimesError`; dropping a linear value without consuming it
triggers `LinearUnusedError`.

| Pattern | API |
|---------|-----|
| Transform (consume → new array) | `append`, `cons`, `set`, `reversed`, `map`, `filter` |
| Terminal read (consume array) | `length`, `get`, `head`, `sum`, `reduce`, `empty` |
| Read and keep array | `get_at` + `got_value` / `got_array`; `len_of` + `len_value` / `len_array` |
| Split into two independent arrays | `copy` → `fst_array` / `snd_array` |

`Array.new unit` creates a **fresh** empty buffer (applied action, not a memoised
value). Literal syntax `#[]` / `#[1, 2, 3]` desugars to `new` / `append` chains.

---

## Refinement parameter `p`

```aeon
linear type Array a forall <p : a -> Bool>
```

Every element is known to satisfy predicate `p`. Operations that insert elements
require `(1 x: {v:a | p v})`; reads return `{v:a | p v}`. The measure `size`
threads through transforms so length proofs compose.

---

## Wrapper types

| Type | Purpose |
|------|---------|
| `ArrayPair a` | Two arrays from `copy` (project with `fst_array`, `snd_array`) |
| `ArrayGet a` | Element + array from `get_at` |
| `ArrayLen a` | Length + array from `len_of` |

Wrapper projections are unrestricted; re-enter linear discipline by binding
projected arrays with `let 1`.

---

## Interop

- **`Cuda.upload_*`** consumes a linear host `Array` and returns a `ReadyBuffer`.
- **`Database`**, **`Subprocess`**, and other modules use `Array` for argv lists
  and row materialization with ordinary refinements on top of linearity.

---

## Related reading

- [`Cuda` GPU buffers](cuda.md)
- [State-safe `Database`](database.md)
- [Collection literals in the language guide](index.md#collection-literals)
