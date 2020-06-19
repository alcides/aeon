from multipledispatch import dispatch

from aeon.ast import Var, Literal, Application, Abstraction, TAbstraction, TApplication, If

from sympy import And, Or, Not, Implies, Eq, Ne, Lt, Gt, Ge, Le, Symbol, S, Poly
from sympy.solvers.inequalities import solve_rational_inequalities
from sympy.functions.elementary.piecewise import Piecewise


class SympyTranslationException(Exception):
    pass


'''
Module responsible for converting Aeon statements to Sympy functions to obtain
intervals from condition restrictions.
'''
# Sympy context with native functions
global sympy_context
sympy_context = {
    "+": lambda x: lambda y: x + y,
    "-": lambda x: lambda y: x - y,
    "*": lambda x: lambda y: x * y,
    "/": lambda x: lambda y: x / y,
    "^": lambda x: lambda y: x ^ y,
    "%": lambda x: lambda y: x % y,
    "==": lambda x: lambda y: Eq(x, y),
    "!=": lambda x: lambda y: Ne(x, y),
    "<": lambda x: lambda y: Lt(x, y),
    ">": lambda x: lambda y: Gt(x, y),
    "<=": lambda x: lambda y: Le(x, y),
    ">=": lambda x: lambda y: Ge(x, y),
    # BoolAlg expressions
    "!": lambda x: Not(x),
    "-->": lambda x: lambda y: Implies(x, y),
    "And": lambda x: lambda y: And(x, y),
    "&&": lambda x: lambda y: And(x, y),
    "||": lambda x: lambda y: Or(x, y),
}


def with_variable(rctx, name, variable):
    sympy_context[name] = variable
    return rctx


# =============================================================================
# Convert each Aeon expression to sympy
@dispatch(object, Literal)
def sympy_translate(rctx, literal):
    return literal.value


@dispatch(object, Var)
def sympy_translate(rctx, var):
    # If there is a value for the Var in the context, return the value
    #if var.name in rctx.evalctx:
    #    return rctx.evalctx[var.name]

    if not var.name in sympy_context:
        sympy_context[var.name] = Symbol(var.name)

    return sympy_context[var.name]


@dispatch(object, Application)
def sympy_translate(rctx, app):
    return sympy_translate(rctx,
                           app.target)(sympy_translate(rctx, app.argument))


@dispatch(object, Abstraction)
def sympy_translate(rctx, abst):
    return lambda x: sympy_translate(with_variable(rctx, abst.arg_name, x),
                                     abst.body)


@dispatch(object, TApplication)
def sympy_translate(rctx, tapp):
    return sympy_translate(rctx, tapp.target)


@dispatch(object, TAbstraction)
def sympy_translate(rctx, tabs):
    return sympy_translate(rctx, tabs.body)


@dispatch(object, If)
def sympy_translate(rctx, iif):
    return Piecewise(
        (sympy_translate(rctx, iif.then), sympy_translate(rctx, iif.cond)),
        (sympy_translate(rctx, iif.otherwise), True))


@dispatch(object, object)
def sympy_translate(rctx, node):
    raise SympyTranslationException(
        'Error when sympy translating {}'.format(node))
