from __future__ import annotations

import importlib

from aeon.frontend.parser import parse_type


def p(x):
    print(str(x))
    return 0


def native_import(name):
    return importlib.import_module(name)


prelude = [
    ("native", "(x:String) -> Bottom", eval),
    ("native_import", "(x:String) -> Bottom", native_import),
    ("print", "(x:Top) -> Unit", p),
    ("==", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x == y),
    ("!=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x != y),
    ("<", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x < y),
    ("<=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x <= y),
    (">", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x > y),
    (">=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x >= y),
    ("+", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x + y),
    ("-", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x - y),
    ("*", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x * y),
    ("/", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x / y),
    ("%", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x % y),
]

typing_vars = {}
evaluation_vars = {}

for n, ty, ex in prelude:
    typing_vars[n] = parse_type(ty)
    evaluation_vars[n] = ex
