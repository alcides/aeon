# Aeon Programming language

Aeon is a programming that with a focus on Liquid Types. Liquid types allow developers to be more specific and annotate their types with a predicate.

```
let x : Int = 3;
let x : (x:Int | x > 0) = 3;
let x : (x:Int | x == 0) = 3;
```

In aeon, all three declarations are valid, and each more specific than the previous. Liquid Types are able to restrict the domain of functions, support assertions in the source code and even statically detect violations of state machines.

There are other languages with Liquid Types, such as [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/), [LiquidJava](https://catarinagamboa.github.io/liquidjava.html), or Rust with [Flux](https://flux-rs.github.io/flux/). But while these languages add liquid types to an existing language, aeon is built with support from liquid types from the start.

## The Aeon interpreter

Aeon is implemented as an interpreter written in Python. Despite being slow, it allows us to design [FFI interfaces](#FFI) with Python, supporting the vast ecosystem that Python offers (from numpy to sklearn or tensorflow).

Aeon can be executed directly from PyPI using [uvx](https://github.com/astral-sh/uv):

`uvx --from aeonlang aeon file.ae`

## Hello World

If your aeon file contains a function named `main`, it will be the entrypoint to the program.

```
def main (args:Int) : Unit {
    print "Hello World"
}
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
let a = 1;
let b = a + (b * (c / d));
let c = (a == 1) || ((b >= 2) && (a > b));
let d = if a == 1 then 2 else 2;
let e = Math_max 2 5; # function application uses spaces.
true
```

Arithmetic operators work on both integers and floats:

```
let a = 1.0 + 2.0;
let a = 1.0 - 2.0;
```

## Functions

```
def plus (x:Int) (y:Int) : Int {
    x + y
}

def plus : (x:Int) -> (y:Int) -> Int = \x -> \y -> x+y;
```

The above top-level definitions are equal to each-other. The first version defines a function that takes two arguments, and has them available directly in the body. The second version defines an object of type function from int, to a function from int to int (curried, like Haskell), and defines that object using nested lambda functions.

`\x -> x + 1` is an annonymous lambda function, which can be annotated with the type `(x:Int) -> Int`.

## Types

Types in Aeon can be very expressive. In refined types, `where` can be used interchangeably with `|`:

```
let x : Int = 1;
let y : {z:Int | z > 0} = 2; # 0 would raise a type error!
let w : {z:Int where z > 0} = 2; # equivalent to the above

def plus (x:Int | x > 0) (y:Int | y > 0) : {z:Int | z > x && z > y} {
    x + y
}

let k = 2; # inferred to be {k:Int | k == 2}
let g = plus k x; # inferred to be {g:Int | g > 2 && g > 1}
```

## Imports

Currently, Aeon allows to include other files in the current file, similarly to C's include statement.

```
import "otherfile.ae";
```

You can also import a specific function from a file:

```
import myFunction from "otherfile.ae";
```

## Polymorphism

Aeon supports parametric polymorphism using `forall`:

```
def id : forall t : B, (x : t) -> t = Λ t : B => \x -> x;
```

The kind `B` represents base types, and `*` represents all types. Type abstraction is introduced with `Λ` (capital lambda) and `=>`.

Aeon also supports refinement polymorphism, allowing a refinement predicate to be abstracted over:

```
def id : forall t : B, forall <p : t -> Bool>, (x : t<p>) -> t<p> = Λ t : B => \x -> x;
```

Here, `<p : t -> Bool>` abstracts over a predicate on type `t`, and `t<p>` applies that predicate as a refinement.

<a name="FFI"></a>

## Foreign Function interfaces

Aeon supports interacting with the Python interpreter via the following functions:

```
native : forall a:*, String -> a
native_import : forall a:*, String -> a
```

You can use native to obtain anything you want:

```
let x : {x:Int | x > 0} = native "1+2";
let x : List = native "[1,2,3]";
```

Using native allows you to convert any Python expression in a string to an Aeon object. Note that this is not type-checked statically, so you may write invalid code that will crash like `(native "2+2" : Float)`.

`let numpy = native_import "numpy";` allows developers to import Python modules directly.

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
def fun (i:Int | i > 0) : (j:Int | j > i) {
    (?todo : Int)
}
```

This function is incomplete: there is a hole in the program (`?todo`) name todo. If you run this program, the compiler will try to search for an expression to replace the hole with, that has the proper type.

Because liquid types are limited, you can define your target function using decorators. The following decorators are available for guiding synthesis:

### Optimization decorators

```
@minimize(fun 3.0 - 5.0)
def fun (i:Int | i > 0) : Float {
    (?todo : Float)
}
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
