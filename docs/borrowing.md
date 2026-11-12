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

Partial applications that retain a resource are rejected; partial applications
of ordinary values remain available. A fully applied call may observe an owned
variable while evaluating its later arguments:

```aeon
let 1 updated := Array.set xs (Array.length xs - 1) value in ...
```

Supplying `xs` reserves it, and ownership transfers when the function body
starts. Later argument expressions may read it but cannot move or mutate it.
The call cannot also receive a borrowed alias of its owned argument: that borrow
would remain active during mutation. Only direct owned variables (including
annotations and simple aliases) receive this treatment; expressions that produce
an owner perform their own consuming operations as they are evaluated.

To keep ordinary curried evaluation safe, functions taking resources must bind
all remaining parameters before executing their body. `def f (1 xs:...) (n:Int)`
does this naturally. An implementation that consumes `xs` and only then returns
`fun n => ...` is rejected. This also applies to generic owning parameters, which
can be instantiated with a linear type. Computation inside ordinary functions
retains its existing evaluation order.

To support retained partial applications later, function values need a way to
express captured ownership or a borrow lifetime. A borrowed closure would freeze
its owner until the closure's last use; an owning closure would consume the owner
and itself require one-use tracking. Those are distinct language features.
Reordering a function's arguments helps particular call sites but does not solve
this general lifetime problem.

Native FFI bodies remain trusted. They must neither mutate borrowed inputs nor
return references to their owned storage; native function values must also defer
resource access until all their arguments are supplied. The checker cannot inspect arbitrary
Python code to prove those obligations. ReadOnly views supplied to NDArray
callbacks additionally enforce expiration at runtime; they do not provide a
general static lifetime system.
