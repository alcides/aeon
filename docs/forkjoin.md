# `ForkJoin`: refinement-safe parallel computation

`ForkJoin.ae` wraps Python's `concurrent.futures.ThreadPoolExecutor` so **fork**,
**join**, and **shutdown** are checked by the compiler. It combines Aeon's two
static disciplines:

- **Linear types (QTT)** — a `Future` must be joined exactly once; a `Pool` must
  be shut down exactly once.
- **Liquid refinements** — worker counts are positive, `par_map` preserves
  length, and `halves` proves a split covers the original array with two
  non-empty pieces.

Together these make a common class of parallel bugs unrepresentable: forgotten
joins, leaked pools, zero-sized worker pools, and divide-and-conquer splits that
drop or duplicate work. Linearity also blocks data races on unique buffers —
you cannot capture the same linear `Array` in two forked thunks without an
explicit `Array.copy`.

- Source: [`aeon/libraries/ForkJoin.ae`](https://github.com/alcides/aeon/blob/master/aeon/libraries/ForkJoin.ae)
- Bindings: [`aeon/bindings/forkjoin.py`](https://github.com/alcides/aeon/blob/master/aeon/bindings/forkjoin.py)
- Examples: [`examples/ffi/forkjoin_example.ae`](https://github.com/alcides/aeon/blob/master/examples/ffi/forkjoin_example.ae),
  [`examples/ffi/forkjoin_divide.ae`](https://github.com/alcides/aeon/blob/master/examples/ffi/forkjoin_divide.ae)
- Generated reference: [stdlib/ForkJoin.html](stdlib/ForkJoin.html) (from `aeon --doc`)

For the general FFI recipe (`native`, opaque types, uninterpreted measures), see
[Writing FFI bindings for a Python package](ffi).

---

## How refinements make parallelism safer

| Risk in raw `ThreadPoolExecutor` | Aeon static check |
|---|---|
| `max_workers=0` / negative | `pool` / `parallel2` / `par_map` require `{n: Int \| n > 0 && n ≤ 64}` |
| Submit and forget a future | `Future a` is linear → `LinearUnusedError` without `join` |
| `future.result()` twice | linear future already consumed → `LinearUsedTooManyTimesError` |
| Forget `shutdown()` | linear `Pool` unused → `LinearUnusedError` |
| Parallel map silently changes length | `par_map` returns `{ys: Array b \| size ys = size xs}` |
| Recursive split drops an element | `halves` proves `left + right = original` and both ≥ 1 |
| Two tasks mutate the same buffer | linear `Array` cannot be shared across forks without `copy` |

Refinements talk about *values* (counts, sizes); linearity talks about
*ownership*. Safe parallel code needs both: sizes that compose under fork/join,
and handles that cannot be aliased or leaked.

---

## Resource lifecycle

```
pool ──fork──► Forked ──forked_pool──► Pool ──…──► shutdown
                 │
                 └──forked_future──► Future ──join──► value
```

Or the two-task path:

```
pool ──fork2──► Forked2 ──forked2_pool──► Pool ──shutdown──► Unit
                   │
                   ├──forked2_left──► Future a ─┐
                   │                             ├──join2──► Joined2
                   └──forked2_right─► Future b ─┘
```

| Handle | Role |
|--------|------|
| `Pool` | Linear thread pool; thread through forks, finish with `shutdown` |
| `Future a` | Linear pending result; must `join` (or `join_timeout`) exactly once |
| `Forked a` / `Forked2 a b` | Unrestricted wrappers that reintroduce the pool + future(s) |
| `Invoked a` | Pool + value after `invoke` (fork+join in one step) |
| `Joined2 a b` | Unrestricted pair after `join2` / `parallel2` |
| `Halves a` | Two non-empty contiguous pieces for divide-and-conquer |

Bind every linear result with `let 1`:

```aeon
def const21 (u: Unit) : Int := 21;

def demo (_: Unit) : Int :=
    let 1 p0 := ForkJoin.pool 4 in
    let f := ForkJoin.fork p0 const21 in
    let 1 p1 := ForkJoin.forked_pool f in
    let 1 fut := ForkJoin.forked_future f in
    let v := ForkJoin.join fut in
    let _ := ForkJoin.shutdown p1 in
    v * 2;
```

---

## One-shot helpers

When you do not need to keep the pool open:

```aeon
def twenty (u: Unit) : Int := 20;
def twenty_two (v: Unit) : Int := 22;
def square (x: Int) : Int := x * x;

# Two independent thunks; pool create/join/shutdown is internal.
def both (_: Unit) : Int :=
    let j := ForkJoin.parallel2 2 twenty twenty_two in
    ForkJoin.joined_fst j + ForkJoin.joined_snd j;

# Length-preserving parallel map over a linear array.
def squares (1 xs: (Array Int)) : {ys: (Array Int) | Array.size ys = Array.size xs} :=
    ForkJoin.par_map 4 square xs;
```

---

## Divide-and-conquer with size proofs

`halves` is the refinement-level contract for splitting work:

```aeon
def halves (1 xs: {arr: (Array a) | Array.size arr >= 2}) :
    {h: Halves a |
        half_left_size h + half_right_size h = Array.size xs &&
        half_left_size h >= 1 &&
        half_right_size h >= 1}
```

After projecting `half_left` / `half_right`, the solver knows each piece is
non-empty and that the sizes sum to the original — so recursive parallel
forks can re-establish the same preconditions on smaller arrays without
runtime bounds checks.

---

## Minimal example

```aeon
import Array;
import ForkJoin;

def work (u: Unit) : Int := 6 * 7;
def inc (x: Int) : Int := x + 1;

def main (_: Int) : Unit :=
    let 1 xs0 := ((Array.new{Int} unit).append 1).append 2 in
    let 1 xs1 := Array.append xs0 3 in
    let 1 ys := ForkJoin.par_map 2 inc xs1 in
    let j := ForkJoin.parallel2 2 work work in
    print (ForkJoin.joined_fst j + ForkJoin.joined_snd j);
```

Violations (zero workers, unjoined future, unshutdown pool, single-element
`halves`) are type errors, not runtime surprises.
