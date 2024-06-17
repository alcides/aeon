from typing import Any

from sympy import And, Or, Not, Eq, Ne, Lt, Gt, Ge, Le, Symbol
from sympy.core.basic import Basic
from sympy.core.expr import Expr
from sympy.logic.boolalg import to_cnf
from sympy.sets.sets import Set
from sympy.solvers.inequalities import reduce_rational_inequalities

from aeon.core.liquid import LiquidApp, LiquidVar, LiquidTerm, LiquidLiteralInt, LiquidLiteralFloat, LiquidLiteralString

sympy_context = {
    "+": lambda x: lambda y: x + y,
    "-": lambda x: lambda y: x - y,
    "*": lambda x: lambda y: x * y,
    "/": lambda x: lambda y: x / y,
    "%": lambda x: lambda y: x % y,
    "+.": lambda x: lambda y: x + y,
    "-.": lambda x: lambda y: x - y,
    "*.": lambda x: lambda y: x * y,
    "/.": lambda x: lambda y: x / y,
    "%.": lambda x: lambda y: x % y,
    "==": lambda x: lambda y: Eq(x, y),
    "!=": lambda x: lambda y: Ne(x, y),
    "<": lambda x: lambda y: Lt(x, y),
    ">": lambda x: lambda y: Gt(x, y),
    "<=": lambda x: lambda y: Le(x, y),
    ">=": lambda x: lambda y: Ge(x, y),
    # BoolAlg expressions
    "!": lambda x: Not(x),
    "&&": lambda x: lambda y: And(x, y),
    "||": lambda x: lambda y: Or(x, y),
}


def liquid_app_to_sympy(ref: LiquidApp) -> Basic:
    ref_fun = ref.fun
    assert len(ref.args) == 2
    # if ref_fun in sympy_context:
    #    return sympy_context[ref_fun](*[refined_to_sympy_expression(arg) for arg in ref.args])
    if ref_fun == ">":
        arg0 = refined_to_sympy_expression(ref.args[0])
        arg1 = refined_to_sympy_expression(ref.args[1])
        return Gt(arg0, arg1)
    elif ref_fun == "&&":
        arg0 = refined_to_sympy_expression(ref.args[0])
        arg1 = refined_to_sympy_expression(ref.args[1])
        return And(arg0, arg1)
    elif ref_fun == "||":
        arg0 = refined_to_sympy_expression(ref.args[0])
        arg1 = refined_to_sympy_expression(ref.args[1])
        return Or(arg0, arg1)
    elif ref_fun == "<":
        assert len(ref.args) == 2
        arg0 = refined_to_sympy_expression(ref.args[0])
        arg1 = refined_to_sympy_expression(ref.args[1])
        return Lt(arg0, arg1)

    elif ref_fun == ">=":
        arg0 = refined_to_sympy_expression(ref.args[0])
        arg1 = refined_to_sympy_expression(ref.args[1])
        return Ge(arg0, arg1)
    elif ref_fun == "<=":
        arg0 = refined_to_sympy_expression(ref.args[0])
        arg1 = refined_to_sympy_expression(ref.args[1])
        return Le(arg0, arg1)
    elif ref_fun == "==":
        arg0 = refined_to_sympy_expression(ref.args[0])
        arg1 = refined_to_sympy_expression(ref.args[1])
        return Eq(arg0, arg1)
    elif ref_fun == "!=":
        arg0 = refined_to_sympy_expression(ref.args[0])
        arg1 = refined_to_sympy_expression(ref.args[1])
        return Ne(arg0, arg1)
    else:
        raise ValueError(f"Unknown Liquid function {ref_fun}")


def refined_to_sympy_expression(ref: LiquidTerm) -> Any:
    # ref = ty.refinement
    # name = ty.name
    # base_type_str = ty.type

    if isinstance(ref, LiquidApp):
        return liquid_app_to_sympy(ref)

    elif isinstance(ref, LiquidVar):
        return Symbol(ref.name)
    elif isinstance(ref, LiquidLiteralInt):
        return ref.value
    elif isinstance(ref, LiquidLiteralFloat):
        return ref.value
    elif isinstance(ref, LiquidLiteralString):
        return ref.value
    else:
        raise ValueError(f"Unknown Liquid term {ref} : {type(ref)}")

    # return ty.predicate.to_sympy_expression(ty.variable)


def flatten_conditions(lista: list) -> list:
    if not isinstance(lista, list):
        return [lista]

    return [item for sublist in lista for item in flatten_conditions(sublist)]


def conditional_to_interval(cond: list, name: str) -> Set:
    try:
        return reduce_rational_inequalities([cond], Symbol(name), relational=False)
    except Exception as err:
        raise Exception("Failed to do ranged analysis due to: {}".format(err))


def sympy_exp_to_bounded_interval(exp: Expr | Basic) -> Any:

    if isinstance(exp, And):
        return [sympy_exp_to_bounded_interval(x) for x in exp.args]
    elif isinstance(exp, Or):
        return tuple(sympy_exp_to_bounded_interval(x) for x in exp.args)
    elif isinstance(exp, Not):
        # Propagate the not
        exp = to_cnf(exp)
        reduce_rational_inequalities([[exp]], [])
        return [sympy_exp_to_bounded_interval(exp)]
    else:
        return [exp]

    pass
