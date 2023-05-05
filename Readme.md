# Aeon 4

Aeon is a programming languages that features Liquid Types, developed at the University of Lisbon. Unlike [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/) or [LiquidJava](https://catarinagamboa.github.io/liquidjava.html), Aeon was designed from the ground up to have support for Liquid Types.

Aeon is in development, so assume all your programs to break. This 4th version is implemented as a Python interpreter, giving you access to any code written in Python.


## Examples


### Hello World

```
def main (args:Int) : Unit {
    print "Hello World"
}
```

To execute this program, you can run:

`python -m aeon examples/hello_world.ae`


### Liquid Types

In this example, you can see the refined type `{x:Int | x > 0}` that represents all integers that are greater than 0. You can also see an example of Python FFI, where a python valid expression can be written as string and passed as the argument to the `native` function.

```
def sqrt : (i: {x:Int | x > 0} ) -> Float = native "__import__('math').sqrt";

def main (i:Int) : Unit {
    print (sqrt 25)
}
```


### Math

```
def abs (i:Int) : Int {
    if i > 0 then i else -i
}

def midpoint(a:Int, b:Int) : Int {
    (a + b) / 2
}

def main (i:Int) : Unit {
    print (abs (-3) + midpoint 1 5)
}
```
