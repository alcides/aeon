from __future__ import annotations

import importlib
from typing import Any

from aeon.sugar.parser import parse_type
from aeon.sugar.stypes import SType
from aeon.utils.name import Name

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


native_types: list[Name] = [
    Name("Unit", 0),
    Name("Bool", 0),
    Name("Int", 0),
    Name("Float", 0),
    Name("String", 0),
    Name("Set", 0),
    Name("Tensor", 0),
    Name("GpuConfig", 0),
]


def gpu_run(k):
    def with_config(c):
        def with_input(t):
            print(f"Executing kernel on CPU (for now) with config {c}...")
            return k(t)

        return with_input

    return with_config


# TODO: polymorphic signatures
prelude = [
    ("native", "forall a:B, (x:String) -> {x:a | false}", eval),
    ("native_import", "forall a:B, (x:String) -> {x:a | false}", native_import),
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
    # SMT Set operations (logical only, used in refinements)
    ("Set_empty", "Set", set()),
    ("Set_sng", "(x:Int) -> Set", lambda x: {x}),
    ("Set_cup", "(a:Set) -> (b:Set) -> Set", lambda a: lambda b: a | b),
    ("Set_cap", "(a:Set) -> (b:Set) -> Set", lambda a: lambda b: a & b),
    ("Set_dif", "(a:Set) -> (b:Set) -> Set", lambda a: lambda b: a - b),
    ("Set_mem", "(x:Int) -> (s:Set) -> Bool", lambda x: lambda s: x in s),
    ("Set_sub", "(a:Set) -> (b:Set) -> Bool", lambda a: lambda b: a <= b),
    (
        "$",
        "forall a:B, forall b:B, forall <p:a -> Bool>, forall <q:b -> Bool>, (f:(x:a<p>) -> b<q>) -> (x:a<p>) -> b<q>",
        lambda f: lambda x: f(x),
    ),
    # GPU helpers (__index__, gpu_map, gpu_imap, gpu_reduce, gpu_filter,
    # gpu_dot, run_gpu) live in the Gpu library and are imported via
    # `open Gpu` / `import Gpu`. See aeon/prelude/gpu.py and libraries/Gpu.ae.
]

typing_vars: dict[Name, SType] = {}
evaluation_vars: dict[Name, Any] = {}


for n, ty, ex in prelude:
    nn = Name(n, 0)
    typing_vars[nn] = parse_type(ty)
    evaluation_vars[nn] = ex
