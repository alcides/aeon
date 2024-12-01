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

To install aeon, you can just run

`pipx install "aeon @ https://github.com/alcides/aeon/archive/master.zip"`

To execute aeon, you can just pass it the name of the file you want to run (file.ae):

`aeon file.ae`


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

| Type    |  Literals     |
|--------:|:--------------|
| Unit    |               |
| Int     | ..., -2, -1, 0, 1, 2, ...   |
| Float   | ..., -2.0, -1.0, 0.0, 1.0, 2.0, ... |
| String  | "", "a", "ab", ... |

### Expressions

Aeon supports most operators that exist in mainstream languages.

```
let a = 1;
let b = a + (b * (c / d));
let c = (a == 1) || ((b => 2) && (a > b));
let d = if a == 1 then 2 else 2;
let e = Math_max 2 5; # function application uses spaces.
True
```

Operators for floats have their own syntax, like in OCam:

```
let a = 1.0 + 2.0;
let a = 1.0 - 2.0;
```

> Float-specific operators are temporary and will be removed once polymorphism support is complete.


## Functions

```
def plus (x:Int) (y:Int) : Int {
    x + y
}

def plus : (x:Int) -> (y:Int) -> Int = \x -> \y -> x+y;
```

The above top-level definitions are equal to each-other. The first version defines a function that takes two arguments, and has them available directly in the body. The second version defines an object of type function from int, to a function from int to int (curried, like Haskell), and defines that object using nested lambda functions.


```\x -> x + 1``` is an annonymous lambda function, which can be annotated with the type ```(x:Int) -> Int```.


## Types

Types in Aeon can be very expressive:

```
let x : Int = 1;
let y : {z:Int | z > >} = 2; # 0 would raise a type error!

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

## Polymorphism

Polymorphism is under development. Stay tuned.

<a name="FFI"></a>
## Foreign Function interfaces

Aeon supports interacting with the Python interpreter via the following functions:

```
native : String -> Bottom
native_import : String -> Bottom
```

Bottom is a special type that is a subtype of any other type. As such, you can use native to obtain anything you want:

```
let x : {x:Int | x > 0} = native "1+2";
let x : List = native "[1,2,3]";
```

Using native allows you to convert any Python expression in a string to an Aeon object. Note that this is not type-checked statically, so you may write invalid code that will crash like `(native "2+2" : Float)`.

`let numpy = native_import "numpy";` allows developers to import Python modules directly.

## Libraries

There are a few libraries available, but unstable as they are under development:

* Image.ae
* List.ae
* Math.ae
* String.ae
* Tuple.ae


## Command-line options

| Flag    |  Description     |
|--------:|:--------------|
| -d      | Prints debug information |
| -t     | Prints timing information about the different steps of the compiler |
| --core | Parses the input file as being the Core language, instead of the surface aeon |


## Synthesis

Aeon supports the automatic synthesis of incomplete code. Take the following example:

```
def fun (i:Int | i > 0) : (j:Int | j > i) {
    (?todo : Int)
}
```

This function is incomplete: there is a hole in the program (`?todo`) name todo. If you run this program, the compiler will try to search for an expression to replace the hole with, that has the proper type.

Because liquid types are limited, you can define your target function:

```
@minimize(fun 3 + fun 5)
def fun (i:Int | i > 0) : (j:Int | j > i) {
    (?todo : Int)
}
```

The minimize decorator will define that the goal of this function is to minimize the sum of `fun 3` and `fun 5`. This allows developers to define targets for their functions, and let the compiler discover proper programs.
