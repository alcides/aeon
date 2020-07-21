import string
import builtins
from .annotation import aefunction, aedocumentation

''' String binds in Aeon to Python '''

@aefunction("""type String;""", None)
class String(object):
    def __init__(self):
        pass

@aefunction('s_equals(a:String, b:String) -> {s:Boolean | s --> (a.size == b.size)};', lambda x: lambda y: equals(x, y))
@aedocumentation("Teste")
def equals(x, y):
    return x == y

@aefunction('s_concat(a:String, b:String) -> {s:String | s.size == a.size + b.size};', lambda x: lambda y: concat(x, y))
def concat(x, y):
    return x + y

@aefunction('ascii(s:{s:String | s.size == 1}) -> Integer;', lambda s: ascii_code(s))
def ascii_code(s):
    return ord(s)

@aefunction('ascii_letters() -> {s:String | s.size == 52};', lambda x: ascii_letters(x))
def ascii_letters(ignored):
    return string.ascii_letters

@aefunction('s_charAt(a:String, i:{i:Integer | i >= 0 && i < a.size}) -> Integer;', lambda x: lambda i: charAt(x, i))
def charAt(x, i):
    return x[i]

@aefunction('s_size(s:String) -> {i:Integer | i == s.size};', lambda x: size(x))
def size(x):
    return builtins.len(x)

@aefunction('s_replace(a:String, b:String, c:String) -> String;', lambda x: lambda y: lambda z: replace(x, y, z))
def replace(x, y, z):
    return z.replace(x, y)

@aefunction('substring(a:String, b:{b:String | a.size <= b.size}) -> Boolean;', lambda x: lambda y: substring(x, y))
def substring(x, y):
    return x in y

@aefunction('s_head(s:{s:String | s.size > 0}) -> {s:String | s.size == 1};', lambda s: head(s))
def head(s):
    return s[0]

@aefunction('s_tail(s:{s:String | s.size > 0}) -> {s2:String | s2.size == s.size - 1};', lambda s: tail(s))
def tail(s):
    return s[1:]

@aefunction('s_count(s:{s:String | s.size == 1}, s2:String) -> {i:Integer | i >= 0 && i <= s2.size};', lambda s: lambda s2: count(s, s2))
def count(s, s2):
    return s2.count(s)

@aefunction('s_forall(f:(x:String -> Boolean), s:String) -> Boolean;', lambda f: lambda s: forall(f, s))
def forall(f, s):
    return all(f(x) for x in s)
    