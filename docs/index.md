# Aeon Programming Language

**Aeon** is a statically-typed functional language built around two ideas that usually live in separate research papers:

1. **Liquid (refinement) types** — types that carry a logical predicate, so the compiler can rule out whole classes of bugs (negative balances, off-by-one errors, division by zero, ...) before the program ever runs. The proof obligations are discharged by an SMT solver (z3).
2. **Program synthesis** — anywhere you would write a value, you can write `?hole` instead. Aeon then searches for an expression that satisfies the surrounding type, optionally minimising or maximising a cost function. Several synthesizers are available (genetic programming, enumerative, SMT-guided, LLM-based, ...).

The two features feed each other: stronger types make synthesis precise (the synthesizer only proposes solutions the type system accepts), and synthesis lets you write *specifications* and let the machine fill in the *implementation*.

```
let age : Int := 25;
let age : {age:Int | age > 0} := 25;
let age : {age:Int | age >= 18 && age < 130} := 25;
```

All three declarations are valid, and each is more specific than the previous. Liquid types restrict the domain of values and functions, support assertions in the source code, and statically catch violations at compile time.

Other languages with liquid types — [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/), [LiquidJava](https://catarinagamboa.github.io/liquidjava.html), or Rust with [Flux](https://flux-rs.github.io/flux/) — bolt liquid types onto an existing language. Aeon was designed around them from the start, which is what allows synthesis to be deeply integrated as well.

## A complete example: types prove safety, synthesis fills the gap

The function below carries its full specification in its type:

* The **preconditions** say `price` is non-negative and `pct` is a real percentage (0–100).
* The **postcondition** says the discounted price is non-negative and never exceeds the original.

```
def apply_discount (price : Int | price >= 0)
                   (pct   : Int | pct >= 0 && pct <= 100)
                 : {r : Int | r >= 0 && r <= price} :=
    price - (price * pct / 100);
```

If the body ever violated those constraints (say, we accidentally wrote `price + pct`), Aeon rejects the program at compile time — no test required, no runtime check inserted.

Now suppose we don't know *the answer*, but we do know *what makes an answer valid*. How small can the yearly deposit be if we want to reach \$10,000 in 20 years at ~1% interest (compound factor ≈ 21.9)? We write the specification and leave a hole:

```
@minimize_int(deposit)
def deposit : {d : Int | d > 0 && d * 21900 >= 10000000} := ?hole;
```

Running this with `uv run python -m aeon --budget 10 -s gp file.ae`, Aeon searches for an integer that satisfies the predicate and is as small as possible — landing on `457` (since `457 * 21900 = 10_008_300`).

The same machinery scales up: holes can appear inside functions, take arguments, and be guided by training data (`@csv_file`), runtime energy use (`@minimize_energy`), or natural-language prompts (`@prompt`, used by the `llm` backend).

## Important concepts when learning Aeon

The list below covers the ideas you'll meet first, with just enough context to get oriented.

| Concept | What it means in Aeon |
|---|---|
| **Refinement types** | Types can carry a logical predicate: `{x:Int \| x > 0}` is the type of positive integers. Preconditions and postconditions live in the type itself and are checked statically by an SMT solver. |
| **Specifications as types** | A function's contract is its type. Once `withdraw : (balance:Int \| balance >= 0) -> (amount:Int \| amount <= balance) -> {r:Int \| r >= 0}` type-checks, the contract is proved — no runtime assertion, no test required. |
| **Immutability** | There is no assignment. `let x := 5` introduces a fresh binding for `x` in the scope that follows; the binding cannot be updated in place. |
| **Currying and space application** | Multi-argument functions are nested single-argument functions. You apply them with whitespace: `add 2 3` is `(add 2) 3`. Partial application is automatic. |
| **Expression-oriented** | Every construct is an expression and returns a value, including `if ... then ... else`. The last expression of a block is the block's value, so there is no separate `return` statement. |
| **No exceptions, no `null`** | Errors are not raised. Failure is modelled with inductive types (`Maybe a`, `Either a b`) or, when possible, ruled out by refinement types so the failure case becomes unrepresentable. |
| **Inductive types and pattern matching** | Data is defined with `inductive` (a sum of named constructors, each carrying typed fields), and destructured with `match ... with`. All constructors must be covered. |
| **Functional, not object-oriented** | There are no classes, methods, or inheritance — only functions and inductive types. Behaviour is composed by passing functions, not by overriding. |
| **Explicit polymorphism** | Generics are introduced with `forall t : B, ...` and applied at the call site, e.g. `id[Int]`. Type abstractions in the body use `Λ` (capital lambda). |
| **Parametric refinements** | A function can be polymorphic over a refinement *predicate*, not just over a type. This lets one definition preserve whatever invariant the caller's arguments happen to satisfy. |
| **Synthesis is a language feature** | `?hole` is a legal expression. The compiler can search for an expression of the surrounding type, optionally guided by `@minimize` / `@maximize` decorators, training data, or natural-language prompts. |
| **Surface syntax** | Top-level definitions use `def`; local bindings use `let`. Function types use `->` (or the Unicode `→`). Comments begin with `#`. |
| **Entry point** | A function `main` returning `Unit` is the program's entry point. Side effects come from primitives like `print` or through the FFI. |
| **Python FFI** | Aeon is implemented as a Python interpreter, so it ships with a direct bridge to Python: `native "expr"` evaluates a Python expression, and `native_import "module"` pulls in a Python module (numpy, sklearn, etc.). The bridge is not statically type-checked, so an incorrect annotation surfaces at runtime. |

## The Aeon interpreter

Aeon is implemented as an interpreter written in Python. Despite being slow, it allows us to design [FFI interfaces](#FFI) with Python, supporting the vast ecosystem that Python offers (from numpy to sklearn or tensorflow).

Aeon can be executed directly from PyPI using [uvx](https://github.com/astral-sh/uv):

`uvx --from aeonlang aeon file.ae`

## Hello World

If your aeon file contains a function named `main`, it will be the entrypoint to the program.

```
def main (args:Int) : Unit :=
    print "Hello World"
```

Main returns Unit, which is the singleton type. It can be used like void in C.

> args should be an array of strings. This is not yet implemented.

`print`receives a string and returns Unit, allowing it to be used inside a main block. Just like in Scala, the last value of a block is its return value.

## Basic Syntax

### Comments

Just like in Python, any line starting with # is a comment.

### Literals

|   Type | Literals                            |
| -----: | :---------------------------------- |
|   Unit |                                     |
|    Int | ..., -2, -1, 0, 1, 2, ...           |
|  Float | ..., -2.0, -1.0, 0.0, 1.0, 2.0, ... |
| String | "", "a", "ab", ...                  |

### Expressions

Aeon supports most operators that exist in mainstream languages.

```
let price := 100;
let total := price + (price * tax / 100);
let eligible := (age >= 18) && (score > 50);
let discount := if price > 50 then 10 else 0;
true
```

#### Unicode operators

Following Lean, several operators accept a Unicode spelling in addition to their
ASCII form. The two are exact aliases — they parse to the same term, so you can
mix and match freely:

| ASCII | Unicode | Meaning |
|---|---|---|
| `!=` | `≠` | inequality |
| `<=` | `≤` | less-or-equal |
| `>=` | `≥` | greater-or-equal |
| `->` | `→` | function-type arrow |
| `=>` | `⇒` or `↦` | lambda / match-branch arrow |

```
def classify : (n:Int) → Int := fun n ↦ if n ≤ 0 then 0 else 1;
```

Boolean implication keeps its ASCII spelling `-->`. (Equality is written `=`, and
definitions use `:=`.)

The formatter (`aeon --format`) normalizes to the Unicode spellings on output, so
`a >= b` and `fun x => ...` are reformatted to `a ≥ b` and `fun x ↦ ...` (Lean's
mapsto arrow).

Function application uses spaces (no parentheses around arguments):

```
open Math
# ...
let result := Math_max 10 20;
```

Arithmetic operators work on both integers and floats:

```
let celsius := 36.6;
let fahrenheit := celsius * 1.8 + 32.0;
```

## Functions

```
def add (x:Int) (y:Int) : Int := x + y;

def add : (x:Int) -> (y:Int) -> Int := fun x => fun y => x + y;
```

The above top-level definitions are equal to each other. The first version defines a function that takes two arguments, and has them available directly in the body. The second version defines an object of type function from int, to a function from int to int (curried, like Haskell), and defines that object using nested lambda functions.

`fun x => x + 1` is an anonymous lambda function (using Lean 4's `fun ... =>` syntax). The argument may be annotated with its type by wrapping it in parentheses: `fun (x:Int) => x + 1`.

### The `$` operator

The `$` operator provides right-associative, low-precedence function application, similar to Haskell:

```
print $ int_to_string $ add 2 3    # equivalent to print (int_to_string (add 2 3))
```

When used with parametrically refined functions, `$` preserves refinements through the application chain.

### Reflecting function bodies into return types (`_`)

By default a top-level function is opaque to the solver: at a call site only its
declared return type is known, and the body is treated as an uninterpreted symbol.
Write `_` as the refinement of a function's return type to *reflect* the body into
the predicate, making the post-condition visible to the SMT solver everywhere the
function is called.

Example:

```
def inc (x:Int) : {y:Int | _} := x + 1;
def witness (x:Int) : {v:Int | v > x} := inc x;
```

`_` expands to `y = x + 1`, so `inc`'s return type becomes `{y:Int | y = x + 1}`.
The proof for `witness` then succeeds because the solver knows `v = x + 1` at the
call site, hence `v > x`.

`if`-then-`else` bodies are reflected too, lowering to `ite` in the predicate, and
`_` can be combined with manual conjuncts:

```
def abs (x:Int) : {y:Int | _} := if x < 0 then (0 - x) else x;
def double_nat (x:{v:Int | v >= 0}) : {y:Int | _ && y >= 0} := x + x;
```

Reflection is rejected with a clear error when the body cannot be encoded as a
predicate: `native` and `uninterpreted` definitions have no symbolic body,
self-referential (recursive) reflection is not yet supported, and some constructs
are not expressible in a refinement. See [`examples/syntax/reflect_underscore.ae`](https://github.com/alcides/aeon/blob/master/examples/syntax/reflect_underscore.ae)
for a full walkthrough.

Before SMT solving, Aeon also simplifies generated verification constraints (boolean identities, redundant equalities, and repeated trivial structure), which helps both solver performance and error-message readability.

## Types

Types in Aeon can be very expressive. In refined types, `where` can be used interchangeably with `|`:

```
let count : Int := 5;
let count : {n:Int | n > 0} := 5;            # 0 would raise a type error!
let count : {n:Int where n > 0} := 5;        # equivalent to the above

def divide (num:Int) (den:Int | den != 0) : Int :=
    native "num // den";

def withdraw (balance:Int | balance >= 0) (amount:Int | amount > 0 && amount <= balance)
    : {result:Int | result >= 0} :=
    balance - amount;
```

Aeon infers the most precise type it can for each binding:

```
let balance := 1000;                          # inferred: {balance:Int | balance = 1000}
let remaining := withdraw balance 200;        # inferred: {remaining:Int | remaining >= 0}
```

## Modules and Imports

Aeon has a Lean-style module system. Each `.ae` file is a module whose name matches the file name (without extension). There are three forms of import:

### Qualified import

```
import Math
```

After a qualified import, names from the module are accessed via dot syntax: `Math.pow 2 3`. The dot syntax is desugared internally to `Math_pow`.

### Selective import

```
import Math (pow, abs)
```

This imports only the listed names, making them available unqualified.

### Open import

```
open Math
```

This brings all names from the module into scope unqualified.

### Module resolution

Modules are resolved by searching (in order):

1. The current directory
2. The `libraries/` directory bundled with Aeon
3. Directories listed in the `AEONPATH` environment variable

Import results are cached by resolved path, and circular imports are detected and raise an error.

## Polymorphism

Aeon supports parametric polymorphism using `forall`:

```
def id : forall t : B, (x : t) -> t := Λ t : B => fun x => x;
```

The kind `B` represents base types, and `*` represents all types. Type abstraction is introduced with `Λ` (capital lambda) and `=>`.

### Parametric Refinements

Aeon supports refinement polymorphism, allowing a refinement predicate to be abstracted over. This is useful when a function preserves a refinement without needing to know what the refinement is.

#### Implicit style (inferred)

When a type variable appears with `<p>`, Aeon infers the refinement quantifier automatically:

```
def clamp : (x : Int<p>) -> (lo : Int<p>) -> (hi : Int<p>) -> Int<p> :=
    fun x => fun lo => fun hi => if x < lo then lo else if x > hi then hi else x;
```

The predicate `p` is inferred. Whatever refinement the caller's arguments satisfy, the result is guaranteed to satisfy it too:

```
def main (args:Int) : Unit :=
    temp : Int | temp >= 0 := 50;
    lo : Int | lo >= 0 := 10;
    hi : Int | hi >= 0 := 100;
    result : Int | result >= 0 := clamp temp lo hi;  # refinement preserved!
    print result;
```

#### Explicit style

You can write the refinement quantifier explicitly with `forall <p : T -> Bool>` and introduce it with `Λ`:

```
def wrap : forall t : B, forall <p : t -> Bool>, (x : t | p x) -> {v : t | p v} :=
    Λ t : B => Λ <p : t -> Bool> => fun x => x;

def main (args:Int) : Unit :=
    score : Int | score > 0 := 42;
    safe_score : Int | safe_score > 0 := wrap[Int]{fun n => n > 0} score;
    print safe_score;
```

#### Refinement application

When calling a function with an explicit refinement parameter, use `{predicate}` to supply the refinement:

```
wrap[Int]{fun n => n > 0} score
```

### Inductive types with parametric refinements

Inductive types can also carry abstract refinement parameters, allowing the same data structure to enforce different invariants depending on context:

```
inductive Container forall <p : Int -> Bool>
| mk (value:Int) : Container
```

## Inductive Types and Pattern Matching

Aeon supports user-defined inductive (algebraic) data types with Lean-style `match` expressions.

### Defining inductive types

```
inductive IntList
| empty : IntList
| cons (hd:Int) (tl:IntList) : IntList
```

Each constructor is declared with `|`, followed by its name, arguments, and return type.

### Pattern matching

Use `match ... with` to destructure inductive values:

```
def len (l:IntList) : Int :=
    match l with
    | empty => 0
    | cons hd tl => 1 + (len tl);
```

Each branch binds the constructor's fields by position. The `match` expression is lowered internally to the inductive eliminator (e.g. `IntList_rec`), so all constructors must be covered.

### Measures

Inductive types can declare measure functions with `+`. These are used for refinements on the type itself:

```
inductive MList a
| empty : {e:(MList a) | len e = 0}
| cons (x:a) (y:(MList a)) : {z:(MList a) | len z = (len y + 1)}
+ len (m:(MList a)) : Int
```

<a name="FFI"></a>

## Foreign Function interfaces

Aeon supports interacting with the Python interpreter via the following functions:

```
native : forall a:*, String -> a
native_import : forall a:*, String -> a
```

You can use `native` to evaluate any Python expression:

```
let pi : Float := native "3.14159265";
let primes : List := native "[2, 3, 5, 7, 11]";
```

Using `native` allows you to embed any Python expression as an Aeon value. Note that this is not type-checked statically, so an incorrect type annotation will crash at runtime.

`native_import` allows importing Python modules directly:

```
let numpy := native_import "numpy";
```

For a step-by-step guide to wrapping a whole Python package — covering opaque types, designing refinements, uninterpreted functions, and the axiom-by-`native` pattern — see [Writing FFI bindings for a Python package](ffi).

For a worked case study of taming two especially error-prone modules — turning `KeyError`, ignored exit codes, and shell injection into compile-time errors — see [Typed bindings for `os` and `subprocess`](os-subprocess). The same treatment for HTTP — mandatory timeouts, status codes you can't ignore — is in [Typed bindings for `requests`](http).

## Libraries

There are a few libraries available, but unstable as they are under development:

- Http.ae
- Image.ae
- Learning.ae
- List.ae
- Map.ae
- Math.ae
- OS.ae
- Plot.ae
- PropTesting.ae
- PSB2.ae
- Random.ae
- Set.ae
- Statistics.ae
- String.ae
- Subprocess.ae
- Table.ae
- Testing.ae
- Tuple.ae

The full HTML reference for every standard-library module — generated from the
`.ae` source by `python -m aeon --doc` — lives under [stdlib/](stdlib/). It
documents each module's types, constructors, functions, and uninterpreted
declarations, with refinement types rendered in surface syntax and hover
tooltips on every argument.

To regenerate the reference locally:

```bash
uv run python scripts/build_stdlib_docs.py
# writes docs/stdlib/*.html and docs/stdlib/index.html
```

The generated files are gitignored; they are produced from source by the
`Docs` GitHub Actions workflow and published alongside the rest of this site.

## Command-line options

|   Flag | Description                                                                   |
| -----: | :---------------------------------------------------------------------------- |
|     -d | Prints debug information                                                      |
|     -t | Prints timing information about the different steps of the compiler           |
| -l, --log | Sets the log level (TRACE, DEBUG, INFO, WARNINGS, ERROR, CRITICAL, etc.)  |
| -f, --logfile | Exports the log to a file                                              |
| -n, --no-main | Disables introducing hole in main                                     |
| --test | Runs every `@property` and `@example` as a test and reports pass/fail        |
| --seed | Random seed for `--test` input generation (reproducible for a fixed seed)    |
| --doc  | Generates HTML documentation from the source file                            |
| --doc-output | Output path (file or directory) for the generated `--doc` HTML          |
| -s, --synthesizer | Selects a synthesizer — see [Synthesizers](synthesizers) for a full list and descriptions |
| --synthesis-format | Selects the output format for synthesized holes (default, json)      |
| --budget | Time budget for synthesis in seconds (default: 60)                          |
| --format | Prints a pretty-printed version of the code to stdout                       |
| --fix | Reformats the source file in place using the pretty printer                    |
| -lsp, --language-server-mode | Runs aeon in Language Server Protocol mode               |
| --tcp | Specifies the TCP port or hostname:port for the LSP server                     |

## Synthesis

Aeon supports the automatic synthesis of incomplete code. Take the following example:

```
def next_even (n:Int | n >= 0) : {r:Int | r > n && r % 2 = 0} :=
    (?hole : Int);
```

This function is incomplete: there is a hole in the program (`?hole`). When you run this program with a synthesizer, Aeon will search for an expression to replace the hole with, that satisfies the refined return type.

Because liquid types are limited, you can define your target function using decorators. The following decorators are available for guiding synthesis:

### Optimization decorators

```
@minimize(approx 3.0 - 5.0)
def approx (x:Int | x > 0) : Float :=
    (?hole : Float);
```

- `@minimize(expr)` — minimize the given expression, also extracts training data when the expression matches `f(args) - expected`
- `@maximize(expr)` — maximize the given expression (internally converted to minimization)
- `@minimize_int(expr)` — minimize an integer expression
- `@maximize_int(expr)` — maximize an integer expression
- `@minimize_float(expr)` — minimize a float expression
- `@maximize_float(expr)` — maximize a float expression
- `@multi_minimize_float(expr)` — multi-objective float minimization

### Resource-use objectives

These add extra minimization objectives alongside numeric ones (for example `@minimize_int`). The synthesizer measures how expensive it is to **evaluate** the given expression for each candidate; the expression’s *value* is ignored, so its static type is unconstrained.

- `@minimize_cputime(expr)` — fitness is CPU time in seconds for evaluating `expr` (`time.process_time()` around the evaluation).
- `@minimize_energy(expr)` — fitness is energy in joules for evaluating `expr`. Uses Intel RAPL via the optional `pyRAPL` package when available; otherwise a CPU-time proxy (`cpu_time ×` a fixed watt estimate) so cheaper candidates still score better.

See `examples/synthesis/cputime_energy.ae` for a program that combines correctness and resource objectives.

### Data-driven decorators

- `@csv_data("1.0,2.0,3.0\n4.0,5.0,12.0")` — provide inline CSV training data (last column is expected output)
- `@csv_file("data.csv")` — load training data from a CSV file

### Worked examples (`@example`)

`@example(assertion)` attaches a concrete, `Bool`-valued assertion about a
function — usually an equality between a fully-applied call and its expected
result. A single annotation serves three purposes at once:

```aeon
# Absolute value of an integer.
@example(my_abs (0 - 3) = 3)
@example(my_abs 5 = 5)
def my_abs (x : Int) : Int := if x < 0 then 0 - x else x;
```

- **Documentation** — the assertion is rendered next to the function by
  `--doc`, giving every function a worked, machine-checked example.
- **Test** — `--test` evaluates the assertion and requires it to hold,
  reported alongside `@property` results.
- **Synthesis specification** — when the body is a hole `?`, each example
  contributes a `minimize (if assertion then 0 else 1)` objective, so a
  fitness-based synthesizer is driven to satisfy every example
  (programming-by-example). A numeric `f(args) = expected` example is also
  recorded as a training point for the `decision_tree` synthesizer, which can
  learn a function directly from its examples.

```bash
aeon --test examples/pbt/examples_decorator.ae   # check every @example
aeon --doc  examples/pbt/examples_decorator.ae   # render them into HTML
```

Property-based tests use the related `@property` decorator: it marks a
`Bool`-returning function whose arguments are universally quantified and checked
on random inputs generated from their (refinement-constrained) types under
`--test`.

### Unit testing (`Testing` library)

A `@property` with **no arguments** is just a unit test: one concrete case the
runner evaluates once (use `@property(1)` so it runs a single time). The
`Testing` library gives this a readable vocabulary — every assertion returns a
plain `Bool`, so unit tests and property tests share the same combinators and
the same `--test` runner:

```aeon
open Testing
open Image

# Unit test — one concrete case.
@property(1)
def test_invert_black_is_white : Bool :=
    black := Image.mk 4 4 (Color.mk 0 0 0);
    assertEqual (Image.get_pixel (Image.invert black) 0 0) (Color.mk 255 255 255);

# Property — the colour channels are generated; the assertion must hold for all.
@property
def prop_solid_pixel_is_fill
    (r : {v : Int | v >= 0 && v < 256})
    (g : {v : Int | v >= 0 && v < 256})
    (b : {v : Int | v >= 0 && v < 256}) : Bool :=
    col := Color.mk r g b;
    assertEqual (Image.get_pixel (Image.mk 8 8 col) 0 0) col;
```

Dimensions are checked here with `Image.get_width` / `Image.get_height`, the
runtime accessors whose return type is refined to equal the static `width` /
`height` measures — so the same number the type system proves is the one you
read back at runtime.

Available assertions: `assertTrue` / `assertThat`, `assertFalse`, `assertEqual`,
`assertNotEqual`, the ordering family `assertLess` / `assertLessEqual` /
`assertGreater` / `assertGreaterEqual`, `assertClose` (floating-point tolerance),
and the combinators `both` / `allOf3` / `allOf4` / `allOf5` for grouping several
checks into a single test. See `examples/testing/image_tests.ae` for a full
suite that tests the Image library.

```bash
aeon --test examples/testing/image_tests.ae
```

### Synthesis control decorators

- `@allow_recursion` — allow recursion during synthesis
- `@disable_control_flow` — disable control flow grammar nodes during synthesis
- `@error_fitness(value)` — set the fitness value to use when an exception occurs during synthesis
- `@prompt("description")` — provide a prompt for LLM-based synthesis

#### Hiding a binding from synthesis

To keep a function or variable (such as a fitness/oracle helper) out of the
synthesizer's grammar, shadow it with a `Unit` binding in the hole's scope:

```aeon
def synth (x: Int) : Int := (let oracle := unit in (?hole : Int))
```

Inside the hole, `oracle` now has type `Unit`, so the type-directed grammar
never builds it into a candidate. This relies on ordinary lexical shadowing and
replaces the former `@hide` / `@hide_types` decorators.
