import math
import builtins
from .helper import aefunction


@aefunction('min<T>(a:T, b:T) -> T = native;', lambda x: lambda y: minimum(x, y))
def minimum(x, y):
    return min(x, y)

@aefunction('max<T>(a:T, b:T) -> T = native;', lambda x: lambda y: maximum(x, y))
def maximum(a, b):
    return max(a, b)

@aefunction('abs<T>(value:T) -> T = native;', lambda value: absolute(value))
def absolute(value):
    return abs(value)

@aefunction('ceil(value:Double) -> Integer = native;', lambda value: ceil(value))
def ceil(value):
    return math.ceil(value)

@aefunction('floor(value:Double) -> Integer = native;', lambda value: floor(value))
def floor(value):
    return math.floor(value)

@aefunction('pow<X>(x:X, y:X) -> X = native;', lambda x: lambda y: power(x, y))
def power(x, y):
    return math.pow(x, y)

@aefunction('sqrt<T>(x:T) -> {y:Double | x - y * y < 0.0001} = native;', lambda x: squareroot(x))
def squareroot(x):
    return math.sqrt(x)

@aefunction('intToDouble(x:Integer) -> {y:Double} = native;', lambda x: intToDouble(x))
def intToDouble(x):
    return int(x)