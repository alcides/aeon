""" This file describes the standard library of Aeon """

import z3

import aeon3.frontend
from aeon3.ast import *
from aeon3.libraries.standard import importNative

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
    result = aeon3.frontend.parse_strict(typee)
    result.name = operation
    return result

# Native operations layouts
native_operation = lambda op: ty(op, "temp<T>: (a:T, b:T) -> {{c:T | c == (a {} b)}} = native;".format(op))
typed_unary_operation = lambda op, typee: ty(op, "temp: (a:{}) -> {{c:{} | c == {}a}} = native;".format(typee, typee, op))
typed_native_operation =  lambda op, typee: ty(op, "temp: (a:{}, b:{}) -> {{c:{} | c == (a {} b)}} = native;".format(typee, typee, typee, op))

initial_context = {
    'native': (aeon3.frontend.parse_strict("type Bottom;"), None),
    # Native functions
    "+" : (native_operation('+'), lambda x: lambda y: x + y),
    "-" : (native_operation('-'), lambda x: lambda y: x - y),
    "*" : (native_operation('*'), lambda x: lambda y: x * y),
    "/" : (native_operation('/'), lambda x: lambda y: x / y),
    "^" : (native_operation('^'), lambda x: lambda y: x ^ y),
    "%" : (native_operation('%'), lambda x: lambda y: x % y),
    "<" : (native_operation('<'), lambda x: lambda y: x < y),
    ">" : (native_operation('>'), lambda x: lambda y: x > y),
    "<=" : (native_operation('<='), lambda x: lambda y: x <= y),
    ">=" : (native_operation('>='), lambda x: lambda y: x >= y),
    "==" : (native_operation('=='), lambda x: lambda y: x == y),
    "!=" : (native_operation('!='), lambda x: lambda y: x != y),
    "&&" : (typed_native_operation('&&', 'Boolean'), lambda x : lambda y : (x and y),
                                                     lambda x: lambda y: z3.And(x, y)),
    "||" : (typed_native_operation('||', 'Boolean'), lambda x: lambda y: x or y,
                                                     lambda x: lambda y: z3.Or(x, y)),
    "-->" : (typed_native_operation('-->', 'Boolean'), lambda x: lambda y: (not x) or y,
                                                       lambda x: lambda y: z3.Implies(x, y)),
    "!" : (typed_unary_operation('!', 'Boolean'), lambda x: not x,
                                                  lambda x: z3.Not(x)),   
}

native_declarations = aeon3.frontend.parse('aeon3/libraries/native.ae')
native_implementations = importNative('aeon3.libraries.native', '*')

for expr in native_declarations.declarations:
    if type(expr) is Definition and type(expr.body) is Var and expr.body.name == 'native':
        add_function(expr.name, (expr, native_implementations[expr.name]))