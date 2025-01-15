from __future__ import annotations

import importlib
from typing import Any

from aeon.sugar.parser import parse_type
from aeon.sugar.stypes import SType

INTEGER_ARITHMETIC_OPERATORS = ["+", "*", "-", "/", "%"]
COMPARISON_OPERATORS = ["<", ">", "<=", ">="]
LOGICAL_OPERATORS = ["&&", "||"]
EQUALITY_OPERATORS = ["==", "!="]

ALL_OPS = INTEGER_ARITHMETIC_OPERATORS + COMPARISON_OPERATORS + LOGICAL_OPERATORS + EQUALITY_OPERATORS


def p(x):
    print(str(x))
    return 0


def native_import(name):
    return importlib.import_module(name)


native_types = ["Unit", "Bool", "Int", "Float", "String"]

# TODO: polymorphic signatures
prelude = [
    ("native", "(x:String) -> Bottom", eval),
    ("native_import", "(x:String) -> Bottom", native_import),
    ("print", "forall a:B, (x:a) -> Unit", p),
    ("==", "forall a:B, (x:a) -> (y:a) -> Bool", lambda x: lambda y: x == y),
    ("!=", "forall a:B, (x:a) -> (y:a) -> Bool", lambda x: lambda y: x != y),
    ("<", "forall a:B, (x:a) -> (y:a) -> Bool", lambda x: lambda y: x < y),
    ("<=", "forall a:B, (x:a) -> (y:a) -> Bool", lambda x: lambda y: x <= y),
    (">", "forall a:B, (x:a) -> (y:a) -> Bool", lambda x: lambda y: x > y),
    (">=", "forall a:B, (x:a) -> (y:a) -> Bool", lambda x: lambda y: x >= y),
    ("+", "forall a:B, (x:a) -> (y:a) -> a", lambda x: lambda y: x + y),
    ("-", "forall a:B, (x:a) -> (y:a) -> a", lambda x: lambda y: x - y),
    ("*", "forall a:B, (x:a) -> (y:a) -> a", lambda x: lambda y: x * y),
    ("/", "forall a:B, (x:a) -> (y:a) -> a", lambda x: lambda y: x / y),
    ("%", "(x:Int) -> (y:Int) -> Int", lambda x: lambda y: x % y),
    ("&&", "(x:Bool) -> (y:Bool) -> Bool", lambda x: lambda y: x and y),
    ("||", "(x:Bool) -> (y:Bool) -> Bool", lambda x: lambda y: x or y),
    ("!", "(x:Bool) -> Bool", lambda x: not x),
]

typing_vars: dict[str, SType] = {}
evaluation_vars: dict[str, Any] = {}

for n, ty, ex in prelude:
    typing_vars[n] = parse_type(ty)
    evaluation_vars[n] = ex
