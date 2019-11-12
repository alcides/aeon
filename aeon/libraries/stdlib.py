""" This file describes the standard library of Aeon """

import aeon.frontend2 as frontend2

import aeon.frontend
from aeon.ast import Var, Definition
from aeon.libraries.standard import importNative


def is_builtin(name):
    return name in initial_context.keys()


def get_builtin_type(name):
    """ Returns the type of a builtin value """
    return initial_context[name][0]


def get_builtin_value(name):
    """ Returns the value needed to execute the builtin function """
    return initial_context[name][1]


def get_all_builtins():
    return list(initial_context.keys())


def add_function(key, value):
    initial_context[key] = value


def ty(operation, typee):
    program = aeon.frontend.parse_strict(typee)
    result = program.declarations[0]
    result.name = operation
    return result


ty2 = frontend2.typee.parse_strict

initial_context = {
    'native': (ty2("Bottom"), None),
    '==':
    (ty2("(T:*) => (a:T) -> (b:T) -> Boolean"), lambda x: lambda y: x == y),
    '!=':
    (ty2("(T:*) => (a:T) -> (b:T) -> Boolean"), lambda x: lambda y: x != y),
    '+':
    (ty2("(T:*) => (a:T) -> (b:T) -> {x:T where (x == ((smtPlus[T] a) b))}"),
     lambda x: lambda y: x + y),
    '-': (ty2("(T:*) => (a:T) -> (b:T) -> T"), lambda x: lambda y: x - y),
    '*': (ty2("(T:*) => (a:T) -> (b:T) -> T"), lambda x: lambda y: x * y),
    '/': (ty2("(T:*) => (a:T) -> (b:{z:T where (z != 0)}) -> T"),
          lambda x: lambda y: x / y),
    '^': (ty2("(T:*) => (a:T) -> (b:T) -> T"), lambda x: lambda y: x ^ y),
    '%': (ty2("(T:*) => (a:T) -> (b:{z:T where (z != 0)}) -> T"),
          lambda x: lambda y: x % y),
    '<':
    (ty2("(T:*) => (a:T) -> (b:T) -> Boolean"), lambda x: lambda y: x < y),
    '>': (ty2("(T:*) => (a:T) -> (b:T) -> Boolean"),
          lambda x: lambda y: x > y),
    '<=': (ty2("(T:*) => (a:T) -> (b:T) -> Boolean"),
           lambda x: lambda y: x <= y),
    '>=': (ty2("(T:*) => (a:T) -> (b:T) -> Boolean"),
           lambda x: lambda y: x >= y),
    '&&': (ty2("(a:Boolean) -> (b:Boolean) -> Boolean"),
           lambda x: lambda y: x and y),
    '||': (ty2("(a:Boolean) -> (b:Boolean) -> Boolean"),
           lambda x: lambda y: x or y),
    '-->': (ty2("(a:Boolean) -> (b:Boolean) -> Boolean"),
            lambda x: lambda y: (not x) or y),
    "!": (ty2("(a:Boolean) -> Boolean"), lambda x: not x),
    "And": (ty2("(a:Boolean) -> (b:Boolean) -> Boolean"),
            lambda x: lambda y: x and y),
    '@maximize': (ty2("(T:*) => (a:T) -> Boolean"), lambda x: True),
    '@minimize': (ty2("(T:*) => (a:T) -> Boolean"), lambda x: True),
    '@evaluate': (ty2("(T:*) => (a:String) -> Boolean"), lambda x: True),
    'smtPlus': (ty2("(T:*) => (a:T) -> (b:T) -> T"),
                lambda x: lambda y: x + y),
}
"""
native_implementations = importNative('aeon.libraries.native', '*')

for expr_name in native_implementations.keys():
    ntype, implementation = native_implementations[expr_name]
    node = Definition(expr_name, ntype, Var("native"))
    add_function(expr_name, (ntype, implementation))
"""
