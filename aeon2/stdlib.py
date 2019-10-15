""" This file describes the standar library of Aeon """

import z3

from .frontend import typee

ty = typee.parse_strict


def is_builtin(name):
    return name in initial_context.keys()


def is_builtin_in_z3(name):
    return name in initial_context.keys() and len(initial_context[name]) >= 3


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


initial_context = {
    'native': (ty("Bottom"), None),
    'uninterpreted': (ty("Bottom"), None),
    "+": (ty("(a:Integer) -> (b:Integer) -> {c:Integer where (c == (a + b))}"),
          lambda x: lambda y: x + y),
    "-": (ty("(a:Integer) -> (b:Integer) -> {c:Integer where (c == (a - b))}"),
          lambda x: lambda y: x - y),
    "*": (ty("(a:Integer) -> (b:Integer) -> {c:Integer where (c == (a * b))}"),
          lambda x: lambda y: x * y),
    "/": (
        ty("(a:Integer) -> (b:Integer) -> {c:Integer where (c == (a / b))}"
           ),  # safediv?
        lambda x: lambda y: x / y),
    "%": (ty("(a:Integer) -> (b:Integer) -> {c:Integer where (c == (a % b))}"),
          lambda x: lambda y: x % y),
    "==": (ty("(a:Integer) -> (b:Integer) -> {c:Boolean where (a == b)}"),
           lambda x: lambda y: x == y),
    "!=": (ty("(a:Integer) -> (b:Integer) -> {c:Boolean where (a != b)}"),
           lambda x: lambda y: x != y),
    "===": (ty("(a:Boolean) -> (b:Boolean) -> {c:Boolean where (a === b)}"),
            lambda x: lambda y: x == y),
    "!==": (ty("(a:Boolean) -> (b:Boolean) -> {c:Boolean where (a !== b)}"),
            lambda x: lambda y: x != y),
    "&&": (ty("(a:Boolean) -> (b:Boolean) -> {c:Boolean where (a && b)}"),
           lambda x: lambda y: x and y, lambda x: lambda y: z3.And(x, y)),
    "||": (ty("(a:Boolean) -> (b:Boolean) -> {c:Boolean where (a || b)}"),
           lambda x: lambda y: x or y, lambda x: lambda y: z3.Or(x, y)),
    "-->":
    (ty("(a:Boolean) -> (b:Boolean) -> {c:Boolean where (a --> b)}"),
     lambda x: lambda y: (not x) or y, lambda x: lambda y: z3.Implies(x, y)),
    "<": (ty("(a:Integer) -> (b:Integer) -> {c:Boolean where (a < b)}"),
          lambda x: lambda y: x < y),
    "<=": (ty("(a:Integer) -> (b:Integer) -> {c:Boolean where (a <= b)}"),
           lambda x: lambda y: x <= y),
    ">": (ty("(a:Integer) -> (b:Integer) -> {c:Boolean where (a > b)}"),
          lambda x: lambda y: x > y),
    ">=": (ty("(a:Integer) -> (b:Integer) -> {c:Boolean where (a >= b)}"),
           lambda x: lambda y: x >= y),
    "fix": (ty("(a:*) => (f:(x:a) -> a) -> a"), Y),
    "print": (ty("(a:Integer) -> Integer"), std_print),

    # TODO: support for lists
    #"empty_list": ( ty("(T:*) => (_:Void) -> (List T)  "), lambda x: [] ), # todo refine
    #"cons": ( ty("(T:*) => (l:(List T)) -> (e:T) ->  {l2: List T where true} "), lambda l: lambda e: [e] ++ l ), # todo refined
}
