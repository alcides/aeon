# Borrowing and ownership in the standard library

A linear owner is bound with `let 1` and consumed exactly once. A `borrow`
parameter gives a function temporary read access without transferring ownership.
Use borrowed shape queries and copyable element reads before an update, then bind
the update's returned owner. Dispose of the last owner explicitly.

```aeon
import Array;

def update (1 xs:{a:(Array Int) | Array.size a > 0}) (value:Int):Int :=
    let last := Array.length xs - 1 in
    let 1 updated := Array.set xs last value in
    let total := Array.sum updated in
    let _ := Array.dispose updated in
    total;
```

`Copy` means that ordinary reuse cannot alias a linear resource. It is available
for primitive values and immutable List, Maybe, Either, Pair, Ordering, Color and
ByteString values (with `Copy` constraints on container elements). `Array.copy`
requires it; an `Array (Array Int)` must move its elements with `take` or
`map_owned`. A user-defined `Copy` instance must implement an unrestricted
`duplicate` method, which cannot accept a concrete linear handle.

| API family | Borrowing observations | Ownership changes |
| --- | --- | --- |
| Array | length, empty, get/head with Copy, sum, mean, count | set, transforms, take, dispose |
| NDArray | dimension, count, get1/2/3 with Copy, reduce | set/fill, reshape, transforms, take1/2/3, discard |
| Stack / Deque | length, empty, peek with Copy | push/pop, with_pop, discard |
| Statistics | numeric summaries and newly allocated result arrays | refinement witness transforms retain ownership transfer |
| DataFrame / LearningCore | shape, column names, scalar predicates; numeric column extraction allocates | updates, fitting, copying, scoring, disposal |
| Reader / Iterator / Random | byte, availability flag, copyable next value, drawn scalar | successor extraction consumes its linear result token |
| ForkJoin / CUDA | immutable metadata | linear result wrappers unpack once into all their owned fields |

`with_pair`, `with_datasets`, `with_halves`, `with_forked`, `with_joined`, and the
CUDA `with_*_download` helpers consume a wrapper once and pass its fields to a
one-use continuation. Repeated owned projections are rejected. Scalar random
draws and batch samples require explicit disposal at the end of a chain. A
borrowed batch-sample observation returns a fresh Float array.

## Curried calls and the second argument

A borrow remains active while later arguments are evaluated and until the full
call returns. Multiple read borrows of the same owner are allowed:

```aeon
def same_length (borrow a:(Array Int)) (borrow b:(Array Int)):Bool :=
    Array.length a = Array.length b;
```

`same_length xs xs` is valid. These forms are rejected:

```aeon
let at := Array.get xs in ...                  # retained partial borrow
read xs (let _ := Array.dispose xs in 0)       # move during an active borrow
```

The full application rule avoids implicit, untracked lifetimes for partial
applications. An argument expression is evaluated from left to right; compute
any observation needed for a consuming update before supplying its owner.

For example, `Array.set xs (Array.length xs - 1) value` is rejected: supplying
the first argument moves `xs`, so the second argument cannot borrow it. Write:

```aeon
let last := Array.length xs - 1 in
let 1 updated := Array.set xs last value in ...
```

A future two-phase rule could reserve the owner at the first argument and move
it only when the complete call starts. While reserved, later arguments could
read it but could neither move nor mutate it. Such a rule must also define
which curried functions defer effects until full application; applying an
arbitrary function to its first argument can itself perform work. It is not
enough to postpone the check while keeping those evaluation semantics.

To support retained partial applications later, function values need a way to
express captured ownership or a borrow lifetime. A borrowed closure would freeze
its owner until the closure's last use; an owning closure would consume the owner
and itself require one-use tracking. Those are distinct language features.
Reordering a function's arguments helps particular call sites but does not solve
this general lifetime problem.

Native FFI bodies remain trusted. They must neither mutate borrowed inputs nor
return references to their owned storage. The checker cannot inspect arbitrary
Python code to prove those obligations. ReadOnly views supplied to NDArray
callbacks additionally enforce expiration at runtime; they do not provide a
general static lifetime system.
