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
| Args / Subprocess | parsed values, exit status, captured output | parsing/running transfers argv; dispose the result after reading it |
| Learning / Models | fitted-model metadata, prediction, scoring, typeclass observations | fit consumes training data; dispose the fitted model after its last read |

`with_pair`, `with_datasets`, `with_halves`, `with_forked`, `with_joined`, and the
CUDA `with_*_download` helpers consume a wrapper once and pass its fields to a
one-use continuation. Repeated owned projections are rejected. Scalar random
draws and batch samples require explicit disposal at the end of a chain. A
borrowed batch-sample observation returns a fresh Float array.

Fitted models and parsed/process results can retain storage transferred by their
input arguments. Bind these results with `let 1`, use their borrowed readers,
then call `dispose_classifier`, `dispose_regressor`, `Args.dispose`, or
`Subprocess.dispose_result`. Generated typeclass methods preserve their declared
`borrow`, `1`, and erased parameter quantities, so `Models.classify` and
`Models.cls_classes` may observe the same fitted model before it is disposed of.

PSB2 benchmarks keep a reusable `TrainingCases` fixture created with
`training_data`. `fresh_train_data` supplies an owned deep copy for one fitness
evaluation. The fixture samples once with seed 0, also keeping independently
started fitness workers on the same cases without resetting search randomness.
`TrainData`, `TestData`, and their unpacked `Tuple` are linear. Use `with_lists`
to consume a training snapshot once and obtain both owned input/output arrays.

## Function quantities and predicate-only locals

Function subtyping preserves usage guarantees. An unrestricted implementation
cannot be assigned a linear or erased parameter signature, and a consuming
implementation cannot masquerade as erased or borrowing. A linear or erased
implementation may be exposed through an unrestricted parameter signature;
trusted multiplicity-polymorphic primitives may instantiate ordinary quantities.

`let 0` is only allowed inside predicates, including refinement expressions.
Executable terms reject erased local definitions, whether inferred, explicitly
typed, or recursive. Erased function parameters remain supported. For example:

```aeon
def keep (x:Int):{v:Int | let 0 expected := x in v = expected} := x;
```

## Curried calls and the second argument

A borrow remains active while later arguments are evaluated and until the full
call returns. Multiple read borrows of the same owner are allowed:

```aeon
def same_length (borrow a:(Array Int)) (borrow b:(Array Int)):Bool :=
    Array.length a = Array.length b;
```

`same_length xs xs` is valid. Moving an owner during a borrowed call is rejected:

```aeon
read xs (let _ := Array.dispose xs in 0)       # move during an active borrow
```

Partial applications may retain ownership when their resulting closure is used
linearly, as described below. Partial applications retaining a read borrow use
the lexical scope rules below. A fully applied call may observe an owned variable while
evaluating its later arguments:

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

## Owning closures and QTT

A closure may capture a linear owner. Creating it transfers the owner into its
environment; the closure must then be bound with `let 1` and consumed exactly
once. This applies to partial applications too:

```aeon
let 1 xs := #[5,9] in
let 1 update := Array.set xs in
let 1 ys := update 0 7 in
Array.consume Array.sum ys
```

After creating `update`, the original `xs` cannot be read, moved, or mutated.
Compute an index before creating the partial application if it needs to inspect
`xs`. The fully applied call rule above still permits nested observations in
later arguments before ownership transfers.

The quantity on a function parameter describes how often that argument is used;
the quantity on a variable holding a function describes how often the function
value is used:

```aeon
def run_once (1 f:(x:Int) -> Int):Int := f 0;

def main (_:Int):Int :=
    let 1 xs := #[5,9] in
    let 1 sum:(x:Int) -> Int := fun x => Array.consume Array.sum xs in
    run_once sum;
```

An owning closure may read its captures before consuming them. A closure which
only reads an external owner instead holds a scoped borrow, described below.
Erased captures have no runtime ownership cost. Captures of unrestricted values
leave ordinary closures and scalar partial applications reusable.

Ownership follows aliases, nested closures, conditional results, polymorphic
transfers, and values stored by consuming constructors. A returned closure keeps
its obligation even when the resource was allocated inside a factory:

```aeon
def make_sum (_:Int):(x:Int) -> Int :=
    let 1 xs := #[5,9] in fun x => Array.consume Array.sum xs;

def use_sum (_:Int):Int := let 1 f := make_sum 0 in f 0;
```

The checker infers these facts from the linked definitions, including imported
and cached modules. A type annotation cannot erase them. Passing a factory to
an unrestricted higher-order parameter cannot hide an owning result; use a `1`
callback parameter and bind its potentially owning results with `let 1`.
Recursive definitions propagate ownership obligations until they stabilize;
ordinary recursive list operations still return reusable lists.
Analysis of opaque results is conservative. In particular,
a non-scalar result of a consuming call may retain ownership even when its
implementation happens to return independent data.

Recursive closures cannot capture owners. Recursive functions can instead take
resources explicitly as `1` parameters and thread their successors through
recursive calls. Owning closures must be consumed once on every branch; copying
them, dropping them, or putting them through unrestricted storage is rejected.
These are static checks and apply with runtime contracts both enabled and
disabled. See `examples/syntax/owning_closures.ae` for a runnable example.

## Scoped borrowed closures

A local closure may retain read borrows without lifetime annotations. The
checker infers its borrowed owners, including through aliases, nested closures,
and partial applications. Such closures are reusable:

```aeon
let 1 xs := #[5,9] in
let total :=
    (let read := Array.get xs in
     read 0 + read 1)
in
let 1 changed := Array.set xs 0 total in
Array.consume Array.sum changed
```

The borrow lasts for the **entire body of the binding** holding the closure.
Within that scope, neither the owner nor an alias may be moved, disposed of,
mutated, or captured by an owning closure. Other reads remain valid. Leaving the
inner scope above ends the loan and allows `Array.set`. A move after the last
call to `read` but still inside its binding's body is rejected; this is lexical
scoping, not inference of the last-use point. Bind an owner explicitly before
partially applying an operation that borrows it.

Borrowed closures cannot escape their scope by being returned or stored in a
container. Returning an independent scalar snapshot or newly allocated data is
allowed. A closure may own one resource and borrow another; it then needs a `1`
binding as well as a scope that preserves its borrowed owner. Erased closures
create no runtime loan. Recursive closures must take resources as parameters
instead of capturing owners or loans.

Use a `borrow` function parameter for a callback that may read its environment:

```aeon
def twice (borrow read:(i:Int) -> Int):Int := read 0 + read 1;

def observe (1 xs:(Array Int)):Int :=
    let total := twice (fun i => Array.length xs + i) in
    let _ := Array.dispose xs in total;
```

The callback may be invoked repeatedly, aliased locally, or passed to another
`borrow` callback parameter. Its loan lasts through later argument evaluation
and the call body. It cannot be returned, stored, or passed to an unrestricted
or `1` parameter, whose signature permits retention. An owning closure, or a
factory returning one, still needs a `1` callback parameter: invoking such a
closure through a reusable borrow could duplicate its ownership obligations.
This uses the existing `borrow` qualifier; no lifetime or region syntax is
required. See `examples/syntax/borrowed_closures.ae` for a runnable example.

## Native implementations

Native FFI bodies remain trusted. They must neither mutate borrowed inputs nor
return references to their owned storage; native function values must also defer
resource access until all their arguments are supplied. Native closures must
also respect declared ownership; arbitrary captures inside Python code are not
inferred. The checker cannot inspect arbitrary
Python code to prove those obligations. ReadOnly views supplied to NDArray
callbacks additionally enforce expiration at runtime; they do not provide a
general static lifetime system.
