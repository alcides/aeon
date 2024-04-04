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

> [!WARNING]
> args should be an array of strings. This is pending.

`print`receives a string and returns Unit, allowing it to be used inside a main block.


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

### let bindings




## Functions

Todo.


## Types

Todo.


## Imports

Todo.

## Polymorphism

Todo.

<a name="FFI"></a>
## Foreign Function interfaces

Todo.

## Libraries

Todo.
