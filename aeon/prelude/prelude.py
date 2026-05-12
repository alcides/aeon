from __future__ import annotations

import importlib
from typing import Any

from aeon.sugar.parser import parse_type
from aeon.sugar.stypes import SType
from aeon.utils.name import Name
from aeon.llvm.utils import RawVector, VectorDType, ensure_raw_vector

INTEGER_ARITHMETIC_OPERATORS = ["+", "*", "-", "/", "%"]
COMPARISON_OPERATORS = ["<", ">", "<=", ">="]
LOGICAL_OPERATORS = ["&&", "||"]
EQUALITY_OPERATORS = ["==", "!="]

ALL_OPS = INTEGER_ARITHMETIC_OPERATORS + COMPARISON_OPERATORS + LOGICAL_OPERATORS + EQUALITY_OPERATORS


def _aeon_vec_new(size: int):
    return RawVector(size, VectorDType.INT)


def _aeon_vec_append(vector: Any, value: Any):
    return ensure_raw_vector(vector).append(value)


def _aeon_vec_get(vector: Any, index: int):
    return ensure_raw_vector(vector).get(index)


def _aeon_vec_set(vector: Any, index: int, value: Any):
    return ensure_raw_vector(vector).set(index, value)


def _aeon_vec_free(vector: Any):
    return ensure_raw_vector(vector).free()


def _aeon_vec_map(fn, vector: Any, size: int):
    source = ensure_raw_vector(vector)
    out = RawVector(size)
    for index in range(size):
        out.set(index, fn(source.get(index)))
    return out


def _aeon_vec_reduce(fn, initial: Any, vector: Any, size: int):
    source = ensure_raw_vector(vector)
    acc = initial
    for index in range(size):
        acc = fn(acc)(source.get(index))
    out = RawVector(1)
    out.set(0, acc)
    return out


def _aeon_vec_imap(fn, vector: Any, size: int):
    source = ensure_raw_vector(vector)
    out = RawVector(size)
    for index in range(size):
        out.set(index, fn(index)(source.get(index)))
    return out


def _aeon_vec_filter(fn, vector: Any, size: int):
    source = ensure_raw_vector(vector)
    return RawVector.from_list([value for index in range(size) if fn(value := source.get(index))])


def _aeon_vec_zipwith(fn, left: Any, right: Any, size: int):
    left_vector = ensure_raw_vector(left)
    right_vector = ensure_raw_vector(right)
    out = RawVector(size)
    for index in range(size):
        out.set(index, fn(left_vector.get(index))(right_vector.get(index)))
    return out


def _aeon_vec_count(fn, vector: Any, size: int):
    source = ensure_raw_vector(vector)
    return sum(1 for index in range(size) if fn(source.get(index)))


def _aeon_vec_size(vector: Any):
    return ensure_raw_vector(vector).size


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
    Name("Vector", 0),
    Name("Set", 0),
]


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
    ("__aeon_vec_new", "forall a:B, (size:Int) -> (Vector a)", _aeon_vec_new),
    (
        "__aeon_vec_append",
        "forall a:B, (v:(Vector a)) -> (x:a) -> (Vector a)",
        lambda v: lambda x: _aeon_vec_append(v, x),
    ),
    ("__aeon_vec_get", "forall a:B, (v:(Vector a)) -> (i:Int) -> a", lambda v: lambda i: _aeon_vec_get(v, i)),
    (
        "__aeon_vec_set",
        "forall a:B, (v:(Vector a)) -> (i:Int) -> (x:a) -> (Vector a)",
        lambda v: lambda i: lambda x: _aeon_vec_set(v, i, x),
    ),
    ("__aeon_vec_free", "forall a:B, (v:(Vector a)) -> Unit", lambda v: _aeon_vec_free(v)),
    (
        "__aeon_vec_map",
        "forall a:B, forall b:B, (f:(x:a) -> b) -> (v:(Vector a)) -> (size:Int) -> (Vector b)",
        lambda f: lambda v: lambda s: _aeon_vec_map(f, v, s),
    ),
    (
        "__aeon_vec_reduce",
        "forall a:B, forall b:B, (f:(acc:a) -> (curr:b) -> a) -> (initial:a) -> (v:(Vector b)) -> (size:Int) -> (Vector a)",
        lambda f: lambda initial: lambda v: lambda s: _aeon_vec_reduce(f, initial, v, s),
    ),
    (
        "__aeon_vec_imap",
        "forall a:B, forall b:B, (f:(i:Int) -> (x:a) -> b) -> (v:(Vector a)) -> (size:Int) -> (Vector b)",
        lambda f: lambda v: lambda s: _aeon_vec_imap(f, v, s),
    ),
    (
        "__aeon_vec_filter",
        "forall a:B, (f:(x:a) -> Bool) -> (v:(Vector a)) -> (size:Int) -> (Vector a)",
        lambda f: lambda v: lambda s: _aeon_vec_filter(f, v, s),
    ),
    (
        "__aeon_vec_zipwith",
        "forall a:B, forall b:B, forall c:B, (f:(x:a) -> (y:b) -> c) -> (v1:(Vector a)) -> (v2:(Vector b)) -> (size:Int) -> (Vector c)",
        lambda f: lambda v1: lambda v2: lambda s: _aeon_vec_zipwith(f, v1, v2, s),
    ),
    (
        "__aeon_vec_count",
        "forall a:B, (f:(x:a) -> Bool) -> (v:(Vector a)) -> (size:Int) -> Int",
        lambda f: lambda v: lambda s: _aeon_vec_count(f, v, s),
    ),
    ("__aeon_vec_size", "forall a:B, (v:(Vector a)) -> Int", lambda v: _aeon_vec_size(v)),
]

typing_vars: dict[Name, SType] = {}
evaluation_vars: dict[Name, Any] = {}


for n, ty, ex in prelude:
    nn = Name(n, 0)
    typing_vars[nn] = parse_type(ty)
    evaluation_vars[nn] = ex
