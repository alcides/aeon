from ctypes import c_bool
from typing import List, Optional
from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralInt,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.types import AbstractionType, BaseType, RefinedType, Type, t_int, t_bool
from aeon.core.terms import Term, Literal, Var, Application, Abstraction, Let


def substitution_in_liquid(t: LiquidTerm, rep: LiquidTerm,
                           name: str) -> LiquidTerm:
    if isinstance(t, LiquidLiteralInt):
        return t
    elif isinstance(t, LiquidLiteralBool):
        return t
    elif isinstance(t, LiquidVar):
        if t.name == name:
            return rep
        else:
            return t
    elif isinstance(t, LiquidApp):
        return LiquidApp(
            t.fun, [substitution_in_liquid(a, rep, name) for a in t.args])
    else:
        print(t, type(t))
        assert False


def substitution_in_type(t: Type, rep: Term, name: str) -> Type:
    replacement: LiquidTerm = liquefy(rep)
    if replacement is None:
        return t

    def rec(t: Type) -> Type:
        return substitution_in_type(t, rep, name)

    if isinstance(t, BaseType):
        return t
    elif isinstance(t, AbstractionType):
        return AbstractionType(t.var_name, rec(t.var_type), rec(t.type))
    elif isinstance(t, RefinedType):
        if t.name == name:
            return t
        else:
            return RefinedType(
                t.name, t.type,
                substitution_in_liquid(t.refinement, replacement, name))


def substitution(t: Term, rep: Term, name: str) -> Term:
    def rec(x: Term):
        return substitution(x, rep, name)

    if isinstance(t, Literal):
        return t
    elif isinstance(t, Var):
        if t.name == name:
            return rep
        return t
    elif isinstance(t, Application):
        return Application(fun=rec(t.fun), arg=rec(t.arg))
    elif isinstance(t, Abstraction):
        if t.var_name == name:
            return t
        else:
            return Abstraction(t.var_name, rec(t.body))
    elif isinstance(t, Let):
        if t.var_name == name:
            n_value = t.value
        else:
            n_value = rec(t.value)
        return Let(t.var_name, n_value, rec(t.body))
    assert False


def liquefy_app(app: Application) -> Optional[LiquidApp]:
    arg = liquefy(app.arg)
    if not arg:
        return None
    if isinstance(app.fun, Var):
        return LiquidApp(app.fun.name, [arg])
    elif isinstance(app.fun, Application):
        liquid_pseudo_fun = liquefy_app(app.fun)
        if liquid_pseudo_fun:
            return LiquidApp(liquid_pseudo_fun.fun,
                             liquid_pseudo_fun.args + [arg])
        return None
    assert False


def liquefy_let(t: Let) -> Optional[LiquidTerm]:
    value = liquefy(t.var_value)
    body = liquefy(t.body)
    if value and body:
        return substitution_in_liquid(body, value, t.var_name)
    return None


def liquefy(rep: Term) -> Optional[LiquidTerm]:
    if isinstance(rep, Literal) and rep.type == t_int:
        return LiquidLiteralInt(rep.value)
    if isinstance(rep, Literal) and rep.type == t_bool:
        return LiquidLiteralBool(rep.value)
    elif isinstance(rep, Application):
        return liquefy_app(rep)
    elif isinstance(rep, Var):
        return LiquidVar(rep.name)
    elif isinstance(rep, Let):
        return liquefy_let(rep)
    assert False
