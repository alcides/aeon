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
    typee = 'temp : {} = native;'.format(typee)
    result = parse_strict(typee)
    result.name = operation
    return result

native_op_template = "temp<T> : (a:T, b:T) -> {{c:T | c == (a {} b)}}"


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
    "!": (ty("!", "(a:Boolean) -> {b:Boolean | (!a == b)}"),
           lambda x: not x, lambda x: z3.Not(x)),
    'And': (ty('And', "(a:Boolean, b:Boolean) -> {c:Boolean | c == (a && b)}"),
            lambda x: lambda y: x and y, lambda x: lambda y: z3.And(x, y)),
    'abs': (ty('abs', "(a:Integer) -> {b:Boolean | b == (a >= 0 ? a : -a)}"),
            lambda x: abs(x)),
    'forall': (ty('forall', "(a:List<T>, f:(T -> Boolean)) -> {c:Boolean | true}"),
            lambda lista: lambda f: all(map(lambda x : f(x), lista))),
    'exists': (ty('exists', "(a:List<T>, f:(T -> Boolean)) -> {c:Boolean | true}"),
            lambda lista: lambda f: any(map(lambda x : f(x), lista))),
    # "fix": (ty("fix", "f : (x:T -> T) -> T"), Y),
    "print": (ty("print", "(a:Integer) -> b:Integer"), std_print),
}
