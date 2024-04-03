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

To execute aeon, you can just pass it the name of the file you want to run: `aeon file.ae` where file.ae is your program.


## Basic Syntax

Todo.


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
