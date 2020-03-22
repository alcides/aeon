import builtins
from .helper import aefunction

@aefunction('equals(a:String, b:String) -> Boolean = native;', lambda x: lambda y: equals(x, y))
def equals(x, y):
    return x == y

@aefunction('concat(a:String, b:String) -> String = native;', lambda x: lambda y: concat(x, y))
def concat(x, y):
    return x + y

@aefunction('size(a:String) -> Integer = native;', lambda x: size(x))
def size(x):
    return builtins.len(x)

@aefunction('replace(a:String, b:String, c:String) -> String = native;', lambda x: lambda y: lambda z: replace(x, y, z))
def replace(x, y, z):
    return z.replace(x, y)

@aefunction('substring(a:String, b:String) -> Boolean = native;', lambda x: lambda y: equals(x, y))
def substring(x, y):
    return x == y
