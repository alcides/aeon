# A guide to writing FFI bindings for a Python package

Aeon runs on top of the Python interpreter, so any Python library — `math`, `numpy`, `sklearn`, `Pillow`, your own package — can become an Aeon module with a thin `.ae` wrapper. The interesting work is not the wiring; it is **deciding what types and refinements to expose** so that Aeon programs using the binding stay statically checked.

This guide walks through the building blocks (`native`, `native_import`, opaque types, uninterpreted functions) and the design questions that come with them. By the end, you should be able to take a Python package and produce a binding that is both ergonomic and verification-friendly.

If you just want to call a one-off Python expression, jump to [§ `native`](#native). If you want to wrap a whole package, read end-to-end.

---

## Table of contents

1. [The mental model](#mental-model)
2. [`native_import` — pulling a package into scope](#native_import)
3. [`native` — calling Python from Aeon](#native)
4. [Opaque types — names for things Aeon doesn't understand](#opaque-types)
5. [Designing refinements](#designing-refinements)
6. [Uninterpreted functions — talking about opaque values](#uninterpreted-functions)
7. [Encoding axioms with `native` no-ops](#axioms)
8. [Multi-argument Python helpers: the `curried` pattern](#curried)
9. [A worked example: wrapping `pathlib`](#worked-example)
10. [Pitfalls and checklist](#pitfalls)

---

<a name="mental-model"></a>

## 1. The mental model

When you write a binding, two layers exist side by side:

| Layer            | Lives in                       | Sees                                                        |
|------------------|--------------------------------|-------------------------------------------------------------|
| Runtime          | The Python interpreter         | Real Python values: ints, floats, `PIL.Image`, `np.ndarray` |
| Refinement logic | Z3, during typechecking        | Aeon types and uninterpreted SMT symbols                    |

`native` and `native_import` bridge the runtime layer. **Opaque types** and **uninterpreted functions** populate the refinement layer with names that talk *about* values the solver cannot inspect.

The two layers must stay consistent — but the language does not enforce it. If you promise in a refinement that `width im == w` and your Python code returns an image of a different size, no compiler will catch the lie. **A binding is a trust boundary**: the wrapper author is responsible for making the refinement layer honest about runtime behaviour.

---

<a name="native_import"></a>

## 2. `native_import` — pulling a package into scope

The prelude defines:

```aeon
native_import : forall a:*, (x:String) -> a
```

At runtime, `native_import "foo"` does `importlib.import_module("foo")` and — importantly — **binds the result into the Python globals under the name of the Aeon definition**. That is what makes the imported module addressable from later `native "..."` strings:

```aeon
def math : Unit = native_import "math"

def PI : Float = native "math.pi"            # <- "math" here is the binding above
def sqrt (i:{v:Float | v >= 0.0}) : Float = native "math.sqrt(i)"
```

Conventions:

- Use **lower-case** names for the binding (`math`, `np`, `plt`, `skl`) so they read naturally inside `native "..."` strings.
- Give it type `Unit`. The actual runtime value is a module object, but you never use it as an Aeon value — only as a Python-side name. Declaring it `Unit` is the idiomatic "I do not intend to use this as a first-class value" marker. (The prelude assigns `native_import` the refinement `{x:a | false}`, so any annotation will type-check; `Unit` is just the least surprising choice.)
- Place all `native_import` calls at the top of the file, immediately after `type` declarations, so a reader can see every Python dependency at a glance.

Examples drawn from the standard library:

```aeon
def math : Unit = native_import "math"
def np : Unit = native_import "numpy"
def plt : Unit = native_import "matplotlib.pyplot"
def skl : Unit = native_import "sklearn"
def json : Unit = native_import "json"
```

For deeper imports you can either `native_import "package.submodule"` or use the `__import__` trick directly inside a `native` string (see [§ multi-argument helpers](#curried) below).

---

<a name="native"></a>

## 3. `native` — calling Python from Aeon

```aeon
native : forall a:*, (x:String) -> a
```

`native "<expression>"` evaluates `<expression>` as a Python expression at runtime. The string is `eval`'d in a context where:

- everything in the Aeon prelude is in scope,
- every Aeon-bound variable visible at the call site is in scope under its Aeon name,
- every name created by `native_import` is in scope.

So inside the body of

```aeon
def pow (i:Int) (j:{v:Int | v >= 0}) : Int = native "i ** j"
```

both `i` and `j` are simply the Python values bound to the formal parameters at runtime. Aeon parameter names become Python identifiers — no marshalling, no wrappers.

The return type of `native` is whatever you declare. Aeon **does not check it**: the prelude gives `native` the refinement `{x:a | false}`, which means the solver cannot derive anything from it, but it also means *you* are asserting the Python expression really returns a value of type `a`. A wrong annotation manifests as a runtime crash (or worse, a silent type confusion).

### When to inline Python vs. when to call into a helper

You have two styles available:

**Inline expression** — concise, fine for one-liners:

```aeon
def abs (i:Int) : {v:Int | v >= 0} = native "abs(i)"
def append (l:(List a)) (i:a) : (List a) = native "l + [i]"
```

**Call into a helper module** — preferred when the logic is non-trivial, when you need imports the wrapper doesn't otherwise pull in, or when a single statement won't do:

```aeon
def Image_open (path:String) : Image =
    native "__import__('aeon.bindings.image').bindings.image.Image_open(path)"
```

The `__import__('pkg.sub').sub.fun(args)` idiom is awkward but lets you call code from any installed Python package without polluting the `.ae` file with an extra `native_import` you do not otherwise need. For substantial bindings (Image, Learning, Table), the convention is to put helpers in `aeon/bindings/<name>.py` and reference them with this pattern.

---

<a name="opaque-types"></a>

## 4. Opaque types — names for things Aeon doesn't understand

Aeon's core types are `Unit`, `Bool`, `Int`, `Float`, `String`, plus user-defined inductives. To talk about *anything else* — a `PIL.Image`, an `sklearn` model, a `pathlib.Path`, a numpy array — declare an **opaque type**:

```aeon
type Image
type Model
type Dataset
type Path
type Plot
```

Opaque types can be parameterised:

```aeon
type List a
type Map k v
type Set a
```

Declaring `type T` adds `T` to the type environment with no structure: Aeon knows `T` is a base type, can pass values of it around, can refine over it, but cannot construct or destruct one without going through `native`. The actual runtime representation is whatever Python value you put there — Aeon never inspects it.

A typical wrapper opens with:

```aeon
type Path

def os : Unit = native_import "os"
def pathlib : Unit = native_import "pathlib"
```

— and from that point on, `Path` is a real Aeon type you can use in signatures, refinements, and synthesis goals.

---

<a name="designing-refinements"></a>

## 5. Designing refinements

Refinements turn a binding from "a Python wrapper" into "a *typed* Python wrapper". The question is always: **what facts about the input or output do I want callers (and the synthesiser) to be able to rely on?**

Three patterns cover most cases.

### 5.1 Refinements on primitive arguments

The easiest case — your Python function has a precondition that can be stated in plain arithmetic:

```aeon
def factorial (i:{v:Int | v >= 0}) : {v:Int | v >= 1} = native "math.factorial(i)"
def sqrt (i:{v:Float | v >= 0.0}) : {v:Float | v >= 0.0} = native "math.sqrt(i)"
def floor_division (i:Int) (j:{v:Int | v != 0}) : Int = native "i // j"
```

These pre/post conditions are checked entirely by Z3 against the caller's arguments. They cost nothing at runtime and turn what would have been a `ValueError` or `ZeroDivisionError` into a compile error.

### 5.2 Refinements on primitive *results*

When the return type's refinement is independent of arguments, just state it:

```aeon
def gcd (i:Int) (j:Int) : {v:Int | v >= 0} = native "math.gcd(i, j)"
def isfinite (i:Float) : Bool = native "math.isfinite(i)"
```

When it depends on arguments, name the result variable and use the parameter names:

```aeon
def clamp
    (x: Int)
    (lo: Int)
    (hi: {v:Int | v >= lo}) :
    {v:Int | v >= lo && v <= hi} =
    native "max(lo, min(x, hi))"
```

Here `lo` flows into the refinement of `hi` *and* into the result refinement — Aeon will pick this up at call sites and let callers reason about the result without re-asserting bounds.

### 5.3 Refinements involving opaque values

This is where it gets interesting. Suppose `Image` is opaque — the solver has no idea what an image *is*. How do you write

```aeon
def crop (im:Image) (x:Int) (y:Int) (w:Int) (h:Int) : Image = ...
```

with a precondition like "the crop rectangle is inside the image" and a postcondition like "the resulting image has dimensions `w × h`"?

The trick is **uninterpreted functions**, covered next.

---

<a name="uninterpreted-functions"></a>

## 6. Uninterpreted functions — talking about opaque values

Declare a function in the refinement language with no body:

```aeon
def width : (im:Image) -> Int = uninterpreted
def height : (im:Image) -> Int = uninterpreted
```

For Z3, these are pure mathematical symbols satisfying only the **congruence axiom**: if `im1 == im2` then `width im1 == width im2`. Z3 will not compute them, simplify them, or substitute into them. It will only relate facts that mention them.

That is enough to write meaningful preconditions and postconditions:

```aeon
def mk
    (w:{p:Int | p > 0})
    (h:{p:Int | p > 0})
    (color:Color) :
    {i:Image | (width i == w) && (height i == h)} =
    native "Image_mk(w, h, color)"

def crop
    (im:Image)
    (x:{p:Int | p >= 0 && p <= width im})
    (y:{p:Int | p >= 0 && p <= height im})
    (w:{p:Int | p > 0 && x + p <= width im})
    (h:{p:Int | p > 0 && y + p <= height im}) :
    {r:Image | (width r == w) && (height r == h)} =
    native "Image_crop(im, x, y, w, h)"
```

Now a call like `crop im 10 10 5000 5000` is a *type error* if `im` is a 100×100 image and the solver can prove it. And every postcondition that mentions `width r == w` enables further reasoning downstream:

```aeon
let resized : {r:Image | width r == 64 && height r == 64} = resize im 64 64
let cropped : {r:Image | width r == 32} = crop resized 0 0 32 32      # OK by transitivity
```

### What you cannot do

Uninterpreted functions are deliberately weak. The solver does *not* know:

- `width (rotate im angle) == width im` — unless you say so (in `rotate`'s return type).
- `width im > 0` for arbitrary `im` — unless you say so (in the type of every function that produces an `Image`).
- That `width` is monotonic, additive, distributive, anything.

Every fact the solver gets is one you encoded by hand, in the return refinement of some constructor or transformer.

### Choosing what to make uninterpreted

Good candidates:

- **Measurable properties** of opaque values that callers will want to reason about (`width`, `height`, `size`, `length`).
- **Boolean predicates** that classify opaque values (`is_balanced` on a dataset; `stream_connected` on a socket).
- **Statistics** that you want to relate across operations but never need to compute symbolically (`sampleMean`, `fracBelow`).

Bad candidates:

- Anything you could compute symbolically with regular Aeon code — write the function and let it be *reflected* into the logic instead of declaring it uninterpreted (see [Reflected functions and PLE](index.md) in the main reference).
- Things that should never appear in a refinement. Keep the uninterpreted surface small.

For inspiration, look at how the standard library declares them:

- `libraries/List.ae` — `size : (l:(List a)) -> Int = uninterpreted`
- `libraries/Set.ae` — `size`, `contains`
- `libraries/Image.ae` — `width`, `height`
- `libraries/Statistics.ae` — a dozen statistical symbols
- `libraries/Socket.ae` — `stream_connected`, `stream_bound`, `payload_len`

---

<a name="axioms"></a>

## 7. Encoding axioms with `native` no-ops

Sometimes the relations between uninterpreted symbols matter. The solver will not figure out, for example, that `fracBelow xs t1 <= fracBelow xs t2` when `t1 <= t2` — `fracBelow` is just a symbol. To inject such a fact, write a **runtime no-op** whose Aeon type asserts it. From `libraries/Statistics.ae`:

```aeon
# Monotonicity below: t1 <= t2 implies fracBelow xs t1 <= fracBelow xs t2.
def widenBelow
    (xs: {x: (List Float) | List.size x > 0})
    (t1: Float)
    (t2: {t: Float | t >= t1})
    : {r: (List Float) | List.size r > 0 && fracBelow r t2 >= fracBelow xs t1}
    = native "xs"
```

`native "xs"` just hands back the input list. The interesting content is the return type: by *consuming* and *returning* the list, the function lets the solver assume — at the call site — that the named relationship holds. Callers thread their list through `widenBelow` to "unlock" the fact for downstream proofs.

This is the standard pattern for axioms over opaque types: a `native`-defined identity (or a wrapper that constructs the appropriate output) whose return refinement is the axiom you want to teach the solver. It is not free — every axiom is a hand-checked promise — but it is how rich theories of opaque types are built.

---

<a name="curried"></a>

## 8. Multi-argument Python helpers: the `curried` pattern

Aeon functions are curried; Python functions are not. When a `native "..."` body needs to call a Python helper that takes more than one argument, the cleanest fix lives on the Python side. The bindings package ships a small decorator:

```python
# aeon/bindings/binding_utils.py
def curried(x, argc=None):
    if argc is None:
        argc = x.__code__.co_argcount
    def p(*a):
        if len(a) == argc:
            return x(*a)
        def q(*b):
            return x(*(a + b))
        return curried(q, argc - len(a))
    return p
```

Apply it to any Python helper you intend to expose:

```python
# aeon/bindings/image.py
from aeon.bindings.binding_utils import curried

@curried
def Image_mk(w, h, c):
    return Image.new("RGB", (w, h), c)
```

Then on the Aeon side you can call it with normal application syntax:

```aeon
def mk
    (w:{p:Int | p > 0})
    (h:{p:Int | p > 0})
    (color:Color) :
    {i:Image | width i == w && height i == h} =
    native "__import__('aeon.bindings.image').bindings.image.Image_mk(w, h, color)"
```

If you only ever pass arguments inside the `native` string (like `Image_mk(w, h, color)` above), the helper is invoked all-at-once and `@curried` is harmless. The decorator pays off when an Aeon function is **partially applied** — say, `mk 64 64` passed to `map` — and Aeon hands a one-arg-at-a-time closure into Python.

---

<a name="worked-example"></a>

## 9. A worked example: wrapping `pathlib`

Putting it together. Suppose we want a small `Path.ae` binding around `pathlib.Path`. We want callers to:

- construct paths,
- ask for length and parent,
- assert that the file exists at the type level, and
- not be allowed to `read_text` on a non-existent path.

```aeon
# libraries/Path.ae

type Path

def pathlib : Unit = native_import "pathlib"
def os : Unit = native_import "os"

# Uninterpreted symbols visible to the solver.
def exists : (p:Path) -> Bool = uninterpreted
def length : (p:Path) -> Int = uninterpreted

# Construct a path from a string. Length is fixed by the source string,
# existence is unknown.
def mk (s:String) : {p:Path | length p == String.size s} =
    native "pathlib.Path(s)"

# Runtime check that lifts existence into the type system.
# If the path does not exist, the caller branches into the else.
def check_exists (p:Path) : {b:Bool | b == exists p} =
    native "p.exists()"

# Only callable on a path the solver knows exists.
def read_text (p:{q:Path | exists q}) : String =
    native "p.read_text()"

# Parent of a path is also a path; we don't claim anything about its length.
def parent (p:Path) : Path =
    native "p.parent"
```

A program using it:

```aeon
def main (args:Int) : Unit =
    p : Path = Path.mk "config.toml";
    if Path.check_exists p then
        print (Path.read_text p)      # OK: branch refines p with `exists p`
    else
        print "missing"
```

Without `check_exists`, calling `read_text p` is a type error — the precondition `exists q` cannot be discharged. With it, the refinement of the branch condition flows into the then-branch and unlocks the call. Note that `exists` and `length` are *never computed* in the refinement logic; they only appear as relations that callers thread through.

---

<a name="pitfalls"></a>

## 10. Pitfalls and checklist

A few things that bite first-time binding authors:

- **`native` annotations are unchecked.** If you write `: Int` over a `native "..."` that returns a string, the program will crash at use, not at the binding. Be conservative.
- **Uninterpreted means *uninterpreted*.** The solver knows nothing about `width` beyond what your function signatures say. If you forget to mention `width r == w` in a constructor's return type, that fact is lost — even though it is trivially true at runtime.
- **Parameter names matter.** They appear inside `native "..."` strings *and* inside refinements. Rename a parameter in one place, rename it in both.
- **Beware shadowing in `native` strings.** The string is `eval`'d with the Aeon environment as Python globals. A binding called `min` will collide with Python's `min`. Stick to lower-case, descriptive, non-builtin names.
- **One `native_import` per package.** Multiple `native_import "math"` definitions all work but create redundant bindings; one is enough.
- **Multi-argument helpers need `@curried`** if Aeon will ever partially apply them.
- **`native_import` calls happen at definition time.** A missing optional dependency will surface as an `ImportError` when the binding file is loaded, not lazily on first use. Guard or factor out optional bindings if that matters for you.

A short checklist for a new binding:

1. `type Foo` for each opaque kind of value the package exposes.
2. `native_import` at the top, lower-case binding names.
3. Uninterpreted symbols for the measurable / boolean properties of `Foo`.
4. Refinement-rich signatures for constructors (output refinements) and transformers (input *and* output refinements).
5. `@curried` Python helpers in `aeon/bindings/<your_name>.py` for anything you cannot express in a single Python expression.
6. Optional: axiom no-ops to inject relations the solver cannot derive.

Browse `libraries/Math.ae`, `libraries/List.ae`, `libraries/Image.ae`, and `libraries/Statistics.ae` for full-sized examples of each pattern in production use.
