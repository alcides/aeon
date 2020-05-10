""" This file describes the standard library of Aeon """

import math
import builtins

import aeon.frontend_core as frontend_core

import aeon.frontend
from aeon.ast import Var, Definition
from aeon.libraries.helper import importNative


def is_builtin(name):
    return name in initial_context.keys()


def get_all_uninterpreted_functions():
    for k in initial_uninterpreted_functions:
        yield (k, initial_uninterpreted_functions[k])


def get_builtin_variables():
    for k in initial_context:
        v = initial_context[k]
        yield (k, v[0], v[1])


def add_function(key, type, implementation):
    initial_context[key] = (type, implementation)


def ty(operation, typee):
    program = aeon.frontend.parse_strict(typee)
    result = program.declarations[0]
    result.name = operation
    return result


ty2 = frontend_core.typee.parse

initial_uninterpreted_functions = {
    '@maximize': ty2("(T:*) => (a:T) -> Boolean"),
    '@minimize': ty2("(T:*) => (a:T) -> Boolean"),
    '@evaluate': ty2("(T:*) => (a:String) -> Boolean"),
    'smtEq': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtIneq': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtLt': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtGt': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtLte': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtGte': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtNot': ty2("(a:Boolean) -> Boolean"),
    'smtImplies': ty2("(a:Boolean) -> (b:Boolean) -> Boolean"),
    'smtAnd': ty2("(a:Boolean) -> (b:Boolean) -> Boolean"),
    'smtOr': ty2("(a:Boolean) -> (b:Boolean) -> Boolean"),
    'smtPlus': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtMinus': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtMult': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtDiv': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtCaret': ty2("(a:Top) -> (b:Top) -> Bottom"),
    'smtMod': ty2("(a:Top) -> (b:Top) -> Bottom"),
    '_String_size': ty2("(a:String) -> Integer"),
}

initial_context = {
    'native': (ty2("Bottom"), None),
    'uninterpreted': (ty2("Bottom"), None),
    '==': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:Boolean where ((smtEq c) ((smtEq a) b))}"
    ), lambda x: lambda y: x == y),
    '!=': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:Boolean where ((smtEq c) ((smtIneq a) b))}"
    ), lambda x: lambda y: x != y),
    '<': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:Boolean where ((smtEq c) ((smtLt a) b))}"
    ), lambda x: lambda y: x < y),
    '>': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:Boolean where ((smtEq c) ((smtGt a) b))}"
    ), lambda x: lambda y: x > y),
    '<=': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:Boolean where ((smtEq c) ((smtLte a) b))}"
    ), lambda x: lambda y: x <= y),
    '>=': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:Boolean where ((smtEq c) ((smtGte a) b))}"
    ), lambda x: lambda y: x >= y),
    'pow': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:Boolean where ((smtEq c) ((smtPow a) b))}"
    ), lambda x: lambda y: math.pow(x, y)),
    'abs': (ty2("(T:*) => (a:T) -> {b:Boolean where ((smtEq c) (smtAbs a))}"),
            lambda x: builtins.abs(x)),
    '&&': (ty2(
        "(a:Boolean) -> (b:Boolean) -> {c:Boolean where ((smtEq c) ((smtAnd a) b))}"
    ), lambda x: lambda y: x and y),
    '||': (ty2(
        "(a:Boolean) -> (b:Boolean) -> {c:Boolean where ((smtEq c) ((smtOr a) b))}"
    ), lambda x: lambda y: x or y),
    '-->': (ty2(
        "(a:Boolean) -> (b:Boolean) -> {c:Boolean where ((smtEq c) ((smtImplies a) b))}"
    ), lambda x: lambda y: (not x) or y),
    "!": (ty2("(a:Boolean) -> {c:Boolean where ((smtEq c) (smtNot a))}"),
          lambda x: not x),
    "And": (ty2(
        "(a:Boolean) -> (b:Boolean) -> {c:Boolean where ((smtEq c) ((smtAnd a) b))}"
    ), lambda x: lambda y: x and y),
    '+':
    (ty2("(T:*) => (a:T) -> (b:T) -> {c:T where ((smtEq c) ((smtPlus a) b))}"),
     lambda x: lambda y: x + y),
    '-': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:T where ((smtEq c) ((smtMinus a) b))}"),
          lambda x: lambda y: x - y),
    '*':
    (ty2("(T:*) => (a:T) -> (b:T) -> {c:T where ((smtEq c) ((smtMult a) b))}"),
     lambda x: lambda y: x * y),
    '/': (ty2(
        "(T:*) => (a:T) -> (b:{z:T where (z != 0)}) -> {c:T where ((smtEq c) ((smtDiv a) b))}"
    ), lambda x: lambda y: x / y),
    '^': (ty2(
        "(T:*) => (a:T) -> (b:T) -> {c:T where ((smtEq c) ((smtCaret a) b))}"),
          lambda x: lambda y: x ^ y),
    '%': (ty2(
        "(a:Integer) -> (b:{z:Integer where (z != 0)}) -> {c:Integer where ((smtEq c) ((smtMod a) b))}"
    ), lambda x: lambda y: x % y),
    '+Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Integer where ((smtEq c) ((smtPlus a) b))}"
    ), lambda x: lambda y: x + y),
    '-Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Integer where ((smtEq c) ((smtMinus a) b))}"
    ), lambda x: lambda y: x - y),
    '*Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Integer where ((smtEq c) ((smtMult a) b))}"
    ), lambda x: lambda y: x * y),
    '/Int': (ty2(
        "(a:Integer) -> (b:{z:Integer where (z != 0)}) -> {c:Integer where ((smtEq c) ((smtDiv a) b))}"
    ), lambda x: lambda y: x / y),
    '==Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Boolean where ((smtEq c) ((smtEq a) b))}"
    ), lambda x: lambda y: x == y),
    '!=Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Boolean where ((smtEq c) ((smtIneq a) b))}"
    ), lambda x: lambda y: x != y),
    '<Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Boolean where ((smtEq c) ((smtLt a) b))}"
    ), lambda x: lambda y: x < y),
    '>Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Boolean where ((smtEq c) ((smtGt a) b))}"
    ), lambda x: lambda y: x > y),
    '<=Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Boolean where ((smtEq c) ((smtLte a) b))}"
    ), lambda x: lambda y: x <= y),
    '>=Int': (ty2(
        "(a:Integer) -> (b:Integer) -> {c:Boolean where ((smtEq c) ((smtGte a) b))}"
    ), lambda x: lambda y: x >= y),
}


def r_print(x):
    print("PRINT: ", x)
    return x


io_context = {
    'print': (ty2("(T:*) => (x:T) -> T"), lambda x: r_print(x)),
}

for expression in io_context.keys():
    ntype, implementation = io_context[expression]
    add_function(expression, ntype, implementation)
