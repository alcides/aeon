# Aeon Programming language

Aeon is a programming that with a focus on Liquid Types. Liquid types allow developers to be more specific and annotate their types with a predicate.

```
let age : Int = 25;
let age : (age:Int | age > 0) = 25;
let age : (age:Int | age >= 18 && age < 130) = 25;
```

In Aeon, all three declarations are valid, and each more specific than the previous. Liquid Types restrict the domain of values and functions, support assertions in the source code, and can statically catch violations at compile time.

There are other languages with Liquid Types, such as [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/), [LiquidJava](https://catarinagamboa.github.io/liquidjava.html), or Rust with [Flux](https://flux-rs.github.io/flux/). But while these languages add liquid types to an existing language, aeon is built with support from liquid types from the start.

## The Aeon interpreter

Aeon is implemented as an interpreter written in Python. Despite being slow, it allows us to design [FFI interfaces](#FFI) with Python, supporting the vast ecosystem that Python offers (from numpy to sklearn or tensorflow).

Aeon can be executed directly from PyPI using [uvx](https://github.com/astral-sh/uv):

`uvx --from aeonlang aeon file.ae`

## Hello World

If your aeon file contains a function named `main`, it will be the entrypoint to the program.

```
def main (args:Int) : Unit =
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
let price = 100;
let total = price + (price * tax / 100);
let eligible = (age >= 18) && (score > 50);
let status = if eligible then 1 else 0;
let best = Math_max score1 score2; # function application uses spaces
true
```

Arithmetic operators work on both integers and floats:

```
let celsius = 36.6;
let fahrenheit = celsius * 1.8 + 32.0;
```

## Functions

```
def add (x:Int) (y:Int) : Int = x + y;

def add : (x:Int) -> (y:Int) -> Int = \x -> \y -> x + y;
```

The above top-level definitions are equal to each other. The first version defines a function that takes two arguments, and has them available directly in the body. The second version defines an object of type function from int, to a function from int to int (curried, like Haskell), and defines that object using nested lambda functions.

`\x -> x + 1` is an anonymous lambda function, which can be annotated with the type `(x:Int) -> Int`.

### The `$` operator

The `$` operator provides right-associative, low-precedence function application, similar to Haskell:

```
print $ int_to_string $ add 2 3    # equivalent to print (int_to_string (add 2 3))
```

When used with parametrically refined functions, `$` preserves refinements through the application chain.

### Reflected functions and PLE

Aeon automatically reflects non-native top-level functions into the logical environment used by refinement checking.
This means the solver can unfold their definitions during verification (PLE-style) instead of treating them as fully uninterpreted symbols.

Example:

```
def inc (x:Int) : Int = x + 1;
def witness (x:Int) : {v:Int | v > x} = inc x;
```

The proof for `witness` succeeds because `inc x` is unfolded to `x + 1` while discharging VCs.

`native` and explicitly `uninterpreted` definitions are not reflected.
Functions with holes are not reflected.

Recursive functions are reflected only when termination evidence is present (for example with `decreasing_by`), so unfolding stays sound.

Before SMT solving, Aeon also simplifies generated verification constraints (boolean identities, redundant equalities, and repeated trivial structure), which helps both solver performance and error-message readability.

## Types

Types in Aeon can be very expressive. In refined types, `where` can be used interchangeably with `|`:

```
let count : Int = 5;
let count : {n:Int | n > 0} = 5;            # 0 would raise a type error!
let count : {n:Int where n > 0} = 5;        # equivalent to the above

def divide (num:Int) (den:Int | den != 0) : Int =
    native "num // den";

def withdraw (balance:Int | balance >= 0) (amount:Int | amount > 0 && amount <= balance)
    : {result:Int | result >= 0} =
    balance - amount;
```

Aeon infers the most precise type it can for each binding:

```
let balance = 1000;                          # inferred: {balance:Int | balance == 1000}
let remaining = withdraw balance 200;        # inferred: {remaining:Int | remaining >= 0}
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
def id : forall t : B, (x : t) -> t = Λ t : B => \x -> x;
```

The kind `B` represents base types, and `*` represents all types. Type abstraction is introduced with `Λ` (capital lambda) and `=>`.

### Parametric Refinements

Aeon supports refinement polymorphism, allowing a refinement predicate to be abstracted over. This is useful when a function preserves a refinement without needing to know what the refinement is.

#### Implicit style (inferred)

When a type variable appears with `<p>`, Aeon infers the refinement quantifier automatically:

```
def clamp : (x : Int<p>) -> (lo : Int<p>) -> (hi : Int<p>) -> Int<p> =
    \x -> \lo -> \hi -> if x < lo then lo else if x > hi then hi else x;
```

The predicate `p` is inferred. Whatever refinement the caller's arguments satisfy, the result is guaranteed to satisfy it too:

```
def main (args:Int) : Unit =
    temp : Int | temp >= 0 = 50;
    lo : Int | lo >= 0 = 10;
    hi : Int | hi >= 0 = 100;
    result : Int | result >= 0 = clamp temp lo hi;  # refinement preserved!
    print result;
```

#### Explicit style

You can write the refinement quantifier explicitly with `forall <p : T -> Bool>` and introduce it with `Λ`:

```
def wrap : forall t : B, forall <p : t -> Bool>, (x : t | p x) -> {v : t | p v} =
    Λ t : B => \x -> x;

def main (args:Int) : Unit =
    score : Int | score > 0 = 42;
    safe_score : Int | safe_score > 0 = wrap[Int] score;
    print safe_score;
```

#### Refinement application

When calling a function with an explicit refinement parameter, use `{predicate}` to supply the refinement:

```
wrap[Int]{\n -> n > 0} score
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
def len (l:IntList) : Int =
    match l with
    | empty => 0
    | cons hd tl => 1 + (len tl);
```

Each branch binds the constructor's fields by position. The `match` expression is lowered internally to the inductive eliminator (e.g. `IntList_rec`), so all constructors must be covered.

### Measures

Inductive types can declare measure functions with `+`. These are used for refinements on the type itself:

```
inductive MList a
| empty : {e:(MList a) | len e == 0}
| cons (x:a) (y:(MList a)) : {z:(MList a) | len z == (len y + 1)}
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
let pi : Float = native "3.14159265";
let primes : List = native "[2, 3, 5, 7, 11]";
```

Using `native` allows you to embed any Python expression as an Aeon value. Note that this is not type-checked statically, so an incorrect type annotation will crash at runtime.

`native_import` allows importing Python modules directly:

```
let numpy = native_import "numpy";
```

## Libraries

There are a few libraries available, but unstable as they are under development:

- Image.ae
- Learning.ae
- List.ae
- Map.ae
- Math.ae
- Plot.ae
- PropTesting.ae
- PSB2.ae
- Random.ae
- Set.ae
- Statistics.ae
- String.ae
- Table.ae
- Tuple.ae

## Command-line options

|   Flag | Description                                                                   |
| -----: | :---------------------------------------------------------------------------- |
|     -d | Prints debug information                                                      |
|     -t | Prints timing information about the different steps of the compiler           |
| -l, --log | Sets the log level (TRACE, DEBUG, INFO, WARNINGS, ERROR, CRITICAL, etc.)  |
| -f, --logfile | Exports the log to a file                                              |
| -n, --no-main | Disables introducing hole in main                                     |
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
def next_even (n:Int | n >= 0) : {r:Int | r > n && r % 2 == 0} =
    (?hole : Int);
```

This function is incomplete: there is a hole in the program (`?hole`). When you run this program with a synthesizer, Aeon will search for an expression to replace the hole with, that satisfies the refined return type.

Because liquid types are limited, you can define your target function using decorators. The following decorators are available for guiding synthesis:

### Optimization decorators

```
@minimize(approx 3.0 - 5.0)
def approx (x:Int | x > 0) : Float =
    (?hole : Float);
```

- `@minimize(expr)` — minimize the given expression, also extracts training data when the expression matches `f(args) - expected`
- `@maximize(expr)` — maximize the given expression (internally converted to minimization)
- `@minimize_int(expr)` — minimize an integer expression
- `@maximize_int(expr)` — maximize an integer expression
- `@minimize_float(expr)` — minimize a float expression
- `@maximize_float(expr)` — maximize a float expression
- `@multi_minimize_float(expr)` — multi-objective float minimization

### Data-driven decorators

- `@csv_data("1.0,2.0,3.0\n4.0,5.0,12.0")` — provide inline CSV training data (last column is expected output)
- `@csv_file("data.csv")` — load training data from a CSV file

### Synthesis control decorators

- `@allow_recursion` — allow recursion during synthesis
- `@disable_control_flow` — disable control flow grammar nodes during synthesis
- `@hide(var1, var2)` — exclude specific variables from the synthesis grammar
- `@hide_types(type1, type2)` — exclude specific types from the synthesis grammar
- `@error_fitness(value)` — set the fitness value to use when an exception occurs during synthesis
- `@prompt("description")` — provide a prompt for LLM-based synthesis
