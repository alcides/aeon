import string
import builtins
from .helper import aefunction

''' String binds in Aeon to Python '''

@aefunction("""type String;""", None)
class String(object):
    def __init__(self):
        pass

@aefunction('equals(a:String, b:String) -> {s:Boolean | s --> (a.size == b.size)} = native;', lambda x: lambda y: equals(x, y))
def equals(x, y):
    return x == y

@aefunction('concat(a:String, b:String) -> {s:String | s.size == a.size + b.size} = native;', lambda x: lambda y: concat(x, y))
def concat(x, y):
    return x + y

@aefunction('ascii({s:String | s.size == 1}) -> Integer = native;', lambda s: ascii_code(s))
def ascii_code(s):
    return ord(s)

@aefunction('ascii_letters() -> {s:String | s.size == 52} = native;', lambda x: ascii_letters(x))
def ascii_letters(ignored):
    return string.ascii_letters

@aefunction('charAt(a:String, {i:Integer | i >= 0 && i < a.size}) -> Integer = native;', lambda x: charAt(x, i))
def charAt(x, i):
    return x[i]

@aefunction('size(s:String) -> {i:Integer | i == s.size} = native;', lambda x: size(x))
def size(x):
    return builtins.len(x)

@aefunction('replace(a:String, b:String, c:String) -> String = native;', lambda x: lambda y: lambda z: replace(x, y, z))
def replace(x, y, z):
    return z.replace(x, y)

@aefunction('substring(a:String, {b:String | a.size <= b.size}) -> Boolean = native;', lambda x: lambda y: substring(x, y))
def substring(x, y):
    return x in y

@aefunction('head({s:String | s.size > 0}) -> {s:String | s.size == 1} = native;', lambda s: head(s))
def head(s):
    return s[0]

@aefunction('tail({s:String | s.size > 0}) -> {s2:String | s2.size == s.size - 1} = native;', lambda s: tail(s))
def tail(s):
    return s[1:]

@aefunction('count({s:String | s.size == 1}, s2:String) -> {i:Integer | i >= 0 && i <= s2.size} = native;', lambda s: lambda s2: count(s, s2))
def count(s, s2):
    return s2.count(s)

@aefunction('forall(f:(x:String -> Boolean), s:String) -> Boolean = native;', lambda f: lambda s: forall(f, s))
def forall(f, s):
    return all(f(x) for x in l)
    