"""Aeon prelude — built-in operators, native types, GPU primitives.

The operator-name list constants and the ``native_types`` Name list
are re-exported from the Rust core (``aeon-rs/src/prelude_consts.rs``).
The Python lambdas / GPU higher-order functions / ``native_import`` /
``eval`` references and the resulting ``typing_vars`` /
``evaluation_vars`` dicts stay Python — they're Python-by-design (live
function references that the evaluator dispatches through Python's
calling protocol, and lark-parsed type signatures).
"""

from __future__ import annotations

import importlib
from typing import Any

from aeon.sugar.parser import parse_type
from aeon.sugar.stypes import SType
from aeon.utils.name import Name

# Static name lists — ported to Rust (aeon-rs/src/prelude_consts.rs);
# re-exported here for backward compatibility with existing imports.
from aeon_rs import ALL_OPS as ALL_OPS
from aeon_rs import COMPARISON_OPERATORS as COMPARISON_OPERATORS
from aeon_rs import EQUALITY_OPERATORS as EQUALITY_OPERATORS
from aeon_rs import INTEGER_ARITHMETIC_OPERATORS as INTEGER_ARITHMETIC_OPERATORS
from aeon_rs import LOGICAL_OPERATORS as LOGICAL_OPERATORS
from aeon_rs import native_types as native_types


def p(x):
    print(str(x))
    return 0


def native_import(name):
    return importlib.import_module(name)


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
    ("unit", "Unit", None),
    ("print", "forall a:B, (x:a) -> Unit", p),
    # Comparison / arithmetic / logical operators are multiplicity-
    # polymorphic — they work for callers at any concrete multiplicity.
    # The ``n`` annotation makes the QTT scaling identity, so passing a
    # linear value into ``+`` doesn't artificially scale it to ``ω``.
    ("==", "forall a:B, (n x:a) -> (n y:a) -> Bool", lambda x: lambda y: x == y),
    ("!=", "forall a:B, (n x:a) -> (n y:a) -> Bool", lambda x: lambda y: x != y),
    ("<", "forall a:B, (n x:a) -> (n y:a) -> Bool", lambda x: lambda y: x < y),
    ("<=", "forall a:B, (n x:a) -> (n y:a) -> Bool", lambda x: lambda y: x <= y),
    (">", "forall a:B, (n x:a) -> (n y:a) -> Bool", lambda x: lambda y: x > y),
    (">=", "forall a:B, (n x:a) -> (n y:a) -> Bool", lambda x: lambda y: x >= y),
    ("+", "forall a:B, (n x:a) -> (n y:a) -> a", lambda x: lambda y: x + y),
    ("-", "forall a:B, (n x:a) -> (n y:a) -> a", lambda x: lambda y: x - y),
    ("*", "forall a:B, (n x:a) -> (n y:a) -> a", lambda x: lambda y: x * y),
    ("/", "forall a:B, (n x:a) -> (n y:a) -> a", lambda x: lambda y: x / y),
    ("%", "(n x:Int) -> (n y:Int) -> Int", lambda x: lambda y: x % y),
    ("&&", "(n x:Bool) -> (n y:Bool) -> Bool", lambda x: lambda y: x and y),
    ("||", "(n x:Bool) -> (n y:Bool) -> Bool", lambda x: lambda y: x or y),
    ("!", "(n x:Bool) -> Bool", lambda x: not x),
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
