from __future__ import annotations

import importlib

from aeon.frontend.parser import parse_type

INTEGER_ARITHMETIC_OPERATORS = ["+", "*", "-", "/", "%"]
FLOAT_ARITHMETIC_OPERATORS = ["+.", "*.", "-.", "/.", "%."]
COMPARISON_OPERATORS = ["<", ">", "<=", ">="]
LOGICAL_OPERATORS = ["&&", "||"]
EQUALITY_OPERATORS = ["==", "!="]

ALL_OPS = (
    INTEGER_ARITHMETIC_OPERATORS
    + FLOAT_ARITHMETIC_OPERATORS
    + COMPARISON_OPERATORS
    + LOGICAL_OPERATORS
    + EQUALITY_OPERATORS
)


def p(x):
    print(str(x))
    return 0


def native_import(name):
    return importlib.import_module(name)


prelude = [
    ("native", "(x:String) -> Bottom", eval),
    ("native_import", "(x:String) -> Bottom", native_import),
    ("print", "(x:Top) -> Unit", p),
    ("&&", "(x:Bool) -> (y:Bool) -> Bool", lambda x: lambda y: x and y),
    ("||", "(x:Bool) -> (y:Bool) -> Bool", lambda x: lambda y: x or y),
    ("==", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x == y),
    ("!=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x != y),
    ("<", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x < y),
    ("<=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x <= y),
    (">", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x > y),
    (">=", "(x:Int) -> (y:Int) -> Bool", lambda x: lambda y: x >= y),
    ("+", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x + y),
    ("+.", "(x:Float) -> (y:Float) -> Float", lambda x: lambda y: x + y),
    ("-", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x - y),
    ("-.", "(x:Float) -> (y:Float) -> Float", lambda x: lambda y: x - y),
    ("*", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x * y),
    ("*.", "(x:Float) -> (y:Float) -> Float", lambda x: lambda y: x * y),
    ("/", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x / y),
    ("/.", "(x:Float) -> (y:Float) -> Float", lambda x: lambda y: x / y),
    ("%", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x % y),
    ("%.", "(x:Float) -> (y:Float) -> Float", lambda x: lambda y: x % y),
]

typing_vars = {}
evaluation_vars = {}

for n, ty, ex in prelude:
    typing_vars[n] = parse_type(ty)
    evaluation_vars[n] = ex
