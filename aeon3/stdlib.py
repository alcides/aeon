""" This file describes the standar library of Aeon """

import z3

from .frontend import parse_strict

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


# Fix = Y
Y = lambda F: F(lambda x: Y(F)(x))


def std_print(x):
    print(x)
    return x

def ty(operation, typee):
    typee = 'define temp : {} = native;'.format(typee)
    result = parse_strict(typee)
    result.name = operation
    return result

initial_context = {
    'native': (parse_strict("type Bottom;"), None),
    "+": (ty("+", "(a:Integer, b:Integer) -> {c:Integer | (c == (a + b))}"),
          lambda x: lambda y: x + y),
    "-": (ty("-", "(a:Integer, b:Integer) -> {c:Integer | (c == (a - b))}"),
          lambda x: lambda y: x - y),
    "*": (ty("*", "(a:Integer, b:Integer) -> {c:Integer | (c == (a * b))}"),
          lambda x: lambda y: x * y),
    "/": (
        ty("/", "(a:Integer, b:Integer) -> {c:Integer | (c == (a / b))}"
           ),  # safediv? 
        lambda x: lambda y: x / y),
    "^": (ty("^", "(a:Integer, b:Integer) -> {c:Integer | (c == (a ^ b))}"),
         lambda x: lambda y: pow(x, y)),
    "%": (ty("%", "(a:Integer, b:Integer) -> {c:Integer | (c == (a % b))}"),
          lambda x: lambda y: x % y),
    "==": (ty("==", "(a:Integer, b:Integer) -> {c:Boolean | (a == b)}"),
           lambda x: lambda y: x == y),
    "!=": (ty("!=", "(a:Integer, b:Integer) -> {c:Boolean | (a != b)}"),
           lambda x: lambda y: x != y),
    "===": (ty("===", "(a:Boolean, b:Boolean) -> {c:Boolean | (a === b)}"),
            lambda x: lambda y: x == y),
    "!==": (ty("!==", "(a:Boolean, b:Boolean) -> {c:Boolean | (a !== b)}"),
            lambda x: lambda y: x != y),
    "&&": (ty("&&", "(a:Boolean, b:Boolean) -> {c:Boolean | (a && b)}"),
           lambda x: lambda y: x and y, lambda x: lambda y: z3.And(x, y)),
    "||": (ty("||", "(a:Boolean, b:Boolean) -> {c:Boolean | (a || b)}"),
           lambda x: lambda y: x or y, lambda x: lambda y: z3.Or(x, y)),
    "-->":
    (ty("-->", "(a:Boolean, b:Boolean) -> {c:Boolean | (a --> b)}"),
     lambda x: lambda y: (not x) or y, lambda x: lambda y: z3.Implies(x, y)),
    "<": (ty("<", "(a:Integer, b:Integer) -> {c:Boolean | (a < b)}"),
          lambda x: lambda y: x < y),
    "<=": (ty("<=", "(a:Integer, b:Integer) -> {c:Boolean | (a <= b)}"),
           lambda x: lambda y: x <= y),
    ">": (ty(">", "(a:Integer, b:Integer) -> {c:Boolean | (a > b)}"),
          lambda x: lambda y: x > y),
    ">=": (ty(">=", "(a:Integer, b:Integer) -> {c:Boolean | (a >= b)}"),
           lambda x: lambda y: x >= y),
    # "fix": (ty("(a:*) => (f:(x:a) -> a) -> a"), Y), TODO:
    "print": (ty("print", "(a:Integer) -> b:Integer"), std_print),
}
