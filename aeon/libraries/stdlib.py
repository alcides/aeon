""" This file describes the standard library of Aeon """

import z3

import aeon.frontend2 as frontend2

import aeon.frontend
from aeon.ast import *
from aeon.libraries.standard import importNative


def is_builtin(name):
    return name in initial_context.keys()


def get_builtin_type(name):
    """ Returns the type of a builtin value """
    return initial_context[name][0]


def get_builtin_value(name):
    """ Returns the value needed to execute the builtin function """
    return initial_context[name][1]


def get_builtin_z3_function(name):
    """ Allows for z3 function definition in some cases """
    definition = initial_context[name]
    if len(definition) > 2:
        return definition[2]
    else:
        return definition[1]


def get_all_builtins():
    return list(initial_context.keys())


def add_function(key, value):
    initial_context[key] = value


def ty(operation, typee):
    program = aeon.frontend.parse_strict(typee)
    result = program.declarations[0]
    result.name = operation
    return result


# Native operations layouts
native_operation = lambda op: ty(
    op, "temp<T>: (a:T, b:T) -> {{c:T | c == (a {} b)}} = native;".format(op)
).type
typed_unary_operation = lambda op, typee: ty(
    op, "temp: (a:{}) -> {{c:{} | c == {}a}} = native;".format(
        typee, typee, op)).type
typed_native_operation = lambda op, typee: ty(
    op, "temp: (a:{}, b:{}) -> {{c:{} | c == (a {} b)}} = native;".format(
        typee, typee, typee, op)).type


# TODO:
def maximize():
    pass


# TODO:
def minimize():
    pass


# TODO:
def evaluate():
    pass


ty2 = frontend2.typee.parse_strict

initial_context = {
    'native': (aeon.frontend.parse_strict("type Bottom;"), None),
    '==':
    (ty2("(T:*) => (a:T) -> (b:T) -> Boolean"), lambda x: lambda y: x == y),
    '!=':
    (ty2("(T:*) => (a:T) -> (b:T) -> Boolean"), lambda x: lambda y: x != y),

    # Native functions
    "+": (native_operation('+'), lambda x: lambda y: x + y),
    "-": (native_operation('-'), lambda x: lambda y: x - y),
    "*": (native_operation('*'), lambda x: lambda y: x * y),
    "/": (native_operation('/'), lambda x: lambda y: x / y),
    "^": (native_operation('^'), lambda x: lambda y: x ^ y),
    "%": (native_operation('%'), lambda x: lambda y: x % y),
    "<": (native_operation('<'), lambda x: lambda y: x < y),
    ">": (native_operation('>'), lambda x: lambda y: x > y),
    "<=": (native_operation('<='), lambda x: lambda y: x <= y),
    ">=": (native_operation('>='), lambda x: lambda y: x >= y),
    #"==": (native_operation('=='), lambda x: lambda y: x == y),
    #"!=": (native_operation('!='), lambda x: lambda y: x != y),
    "&&": (typed_native_operation('&&', 'Boolean'),
           lambda x: lambda y: (x and y), lambda x: lambda y: z3.And(x, y)),
    "||": (typed_native_operation('||', 'Boolean'), lambda x: lambda y: x or y,
           lambda x: lambda y: z3.Or(x, y)),
    "-->":
    (typed_native_operation('-->', 'Boolean'),
     lambda x: lambda y: (not x) or y, lambda x: lambda y: z3.Implies(x, y)),
    "!": (typed_unary_operation('!', 'Boolean'), lambda x: not x,
          lambda x: z3.Not(x)),
    "And": (ty(
        'And',
        'temp: (a:Boolean, b:Boolean) -> {c:Boolean | c == (a && b)} = native;'
    ), lambda x: lambda y: x and y),
    "@maximize":
    (ty('@maximize',
        'temp<T>: (something:T) -> Boolean = native;'), lambda x: True),
    "@minimize": (ty('@minimize',
                     'temp<T>: (something:T) -> Boolean = native;'),
                  lambda x: True),
    "@evaluate": (ty('@evaluate', 'temp: (path:String) -> Boolean = native;'),
                  lambda x: True),
}

native_implementations = importNative('aeon.libraries.native', '*')

for expr_name in native_implementations.keys():
    node, implementation = native_implementations[expr_name]
    add_function(expr_name, (node, implementation))
