import math
import builtins
from .annotation import aefunction, aedocumentation


@aefunction('min[T](a:T, b:T) -> T;')
def minimum(x, y):
    return min(x, y)

@aefunction('max[T](a:T, b:T) -> T;')
def maximum(a, b):
    return max(a, b)

@aefunction('abs[T](value:T) -> T;')
def absolute(value):
    return abs(value)

@aefunction('ceil(value:Double) -> Integer;')
def ceil(value):
    return math.ceil(value)

@aefunction('floor(value:Double) -> Integer;')
def floor(value):
    return math.floor(value)

@aefunction('pow[X, Y](x:X, y:Y) -> Y;')
def power(x, y):
    return math.pow(x, y)

@aefunction('sqrt[T](x:T) -> {y:Double | x - y * y < 0.0001};')
def squareroot(x):
    return math.sqrt(x)

@aefunction('intToDouble(x:Integer) -> Double;')
def intToDouble(x):
    return int(x)