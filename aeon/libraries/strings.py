import string
import builtins
from .annotation import aefunction, aedocumentation

''' String binds in Aeon to Python '''

@aefunction("""type String;""")
class String(object):
    def __init__(self):
        pass

@aefunction('s_equals(a:String, b:String) -> {s:Boolean | s --> (a.size == b.size)};')
@aedocumentation("Teste")
def equals(x, y):
    return x == y

@aefunction('s_concat(a:String, b:String) -> {s:String | s.size == a.size + b.size};')
def concat(x, y):
    return x + y

@aefunction('ascii(s:{s:String | s.size == 1}) -> Integer;')
def ascii_code(s):
    return ord(s)

@aefunction('ascii_letters() -> {s:String | s.size == 52};')
def ascii_letters(ignored):
    return string.ascii_letters

@aefunction('s_charAt(a:String, i:{i:Integer | i >= 0 && i < a.size}) -> Integer;')
def charAt(x, i):
    return x[i]

@aefunction('s_size(s:String) -> {i:Integer | i == s.size};')
def size(x):
    return builtins.len(x)

@aefunction('s_replace(a:String, b:String, c:String) -> String;')
def replace(x, y, z):
    return z.replace(x, y)

@aefunction('substring(a:String, b:{b:String | a.size <= b.size}) -> Boolean;')
def substring(x, y):
    return x in y

@aefunction('s_head(s:{s:String | s.size > 0}) -> {s:String | s.size == 1};')
def head(s):
    return s[0]

@aefunction('s_tail(s:{s:String | s.size > 0}) -> {s2:String | s2.size == s.size - 1};')
def tail(s):
    return s[1:]

@aefunction('s_count(s:{s:String | s.size == 1}, s2:String) -> {i:Integer | i >= 0 && i <= s2.size};')
def count(s, s2):
    return s2.count(s)

@aefunction('s_forall(f:(x:String -> Boolean), s:String) -> Boolean;')
def forall(f, s):
    return all(f(x) for x in s)
    