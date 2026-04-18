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
    Name("Tensor", 0),
    Name("GpuConfig", 0),
]


def gpu_map(f):
    def run(t, conf=None):
        # TODO add gpu support
        return [f(x) for x in t]

    return run


def gpu_imap(f):
    def run(t, conf=None):
        # TODO add gpu support
        return [f(i) for i in range(len(t))]

    return run


def gpu_reduce(f):
    def with_initial(i):
        def run(t, conf=None):
            import functools

            # TODO add gpu support
            return functools.reduce(lambda x, y: f(x)(y), t, i)

        return run

    return with_initial


def gpu_filter(f):
    def run(t, conf=None):
        # TODO add gpu support
        return [x for x in t if f(x)]

    return run


def gpu_dot(a):
    def with_b(b):
        # TODO add gpu support
        return sum(x * y for x, y in zip(a, b))

    return with_b


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
    (
        "$",
        "forall a:B, forall b:B, forall <p:a -> Bool>, forall <q:b -> Bool>, (f:(x:a<p>) -> b<q>) -> (x:a<p>) -> b<q>",
        lambda f: lambda x: f(x),
    ),
    ("gpu_map", "forall a:B, forall b:B, (f:(x:a) -> b) -> (t:Tensor) -> Tensor", gpu_map),
    (
        "gpu_imap",
        "forall b:B, (f:(i:Int) -> b) -> (t:Tensor) -> Tensor",
        gpu_imap,
    ),
    ("__index__", "forall a:B, (t:Tensor) -> (i:Int) -> a", lambda t: lambda i: t[i]),
    (
        "gpu_reduce",
        "forall a:B, (f:(acc:a) -> (x:a) -> a) -> (initial:a) -> (t:Tensor) -> a",
        gpu_reduce,
    ),
    (
        "gpu_filter",
        "forall a:B, (f:(x:a) -> Bool) -> (t:Tensor) -> Tensor",
        gpu_filter,
    ),
    (
        "gpu_dot",
        "(a:Tensor) -> (b:Tensor) -> Float",
        gpu_dot,
    ),
    (
        "run_gpu",
        "forall a:B, (kernel:(x:Tensor) -> a) -> (config:GpuConfig) -> (input:Tensor) -> a",
        gpu_run,
    ),
]

typing_vars: dict[Name, SType] = {}
evaluation_vars: dict[Name, Any] = {}


for n, ty, ex in prelude:
    nn = Name(n, 0)
    typing_vars[nn] = parse_type(ty)
    evaluation_vars[nn] = ex
