from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.types import LiquidHornApplication
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.terms import Abstraction, TypeApplication
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypeVar


def substitute_vartype(t: Type, rep: Type, name: str):
    """Replaces all occurrences of vartypes name in t by rep."""

    def rec(k: Type):
        return substitute_vartype(k, rep, name)

    if isinstance(t, Bottom):
        return t
    elif isinstance(t, Top):
        return t
    elif isinstance(t, BaseType):
        return t
    elif isinstance(t, TypeVar) and t.name == name:
        return rep
    elif isinstance(t, TypeVar) and t.name != name:
        return t
    elif isinstance(t, RefinedType):
        it = RefinedType(t.name, rec(t.type), t.refinement)
        while isinstance(it.type, RefinedType):
            nr = substitution_in_liquid(
                it.type.refinement,
                LiquidVar(t.name),
                it.type.name,
            )
            ncond = LiquidApp("&&", [t.refinement, nr])
            it = RefinedType(t.name, it.type.type, ncond)
        return it
    elif isinstance(t, AbstractionType):
        return AbstractionType(t.var_name, rec(t.var_type), rec(t.type))
    assert False


def substitute_vartype_in_term(t: Term, rep: Type, name: str):

    def rec(x: Term):
        return substitute_vartype_in_term(x, rep, name)

    if isinstance(t, Literal):
        return t
    elif isinstance(t, Var):
        return t
    elif isinstance(t, Hole):
        return t
    elif isinstance(t, Application):
        return Application(fun=rec(t.fun), arg=rec(t.arg))
    elif isinstance(t, Abstraction):
        return Abstraction(t.var_name, rec(t.body))
    elif isinstance(t, Let):
        n_value = rec(t.var_value)
        n_body = rec(t.body)
        return Let(t.var_name, n_value, n_body)
    elif isinstance(t, Rec):
        n_value = rec(t.var_value)
        n_type = substitute_vartype(t.var_type, rep, name)
        n_body = rec(t.body)
        return Rec(t.var_name, n_type, n_value, n_body)
    elif isinstance(t, Annotation):
        n_type = substitute_vartype(t.type, rep, name)
        return Annotation(rec(t.expr), n_type)
    elif isinstance(t, If):
        n_cond = rec(t.cond)
        n_then = rec(t.then)
        n_otherwise = rec(t.otherwise)
        return If(n_cond, n_then, n_otherwise)
    assert False


def substitution_in_liquid(
    t: LiquidTerm,
    rep: LiquidTerm,
    name: str,
) -> LiquidTerm:
    """substitutes name in the term t with the new replacement term rep."""
    assert isinstance(rep, LiquidTerm)
    if isinstance(
        t,
        (
            LiquidLiteralInt,
            LiquidLiteralBool,
            LiquidLiteralString,
            LiquidLiteralFloat,
        ),
    ):
        return t
    elif isinstance(t, LiquidVar):
        if t.name == name:
            return rep
        else:
            return t
    elif isinstance(t, LiquidApp):
        return LiquidApp(
            t.fun,
            [substitution_in_liquid(a, rep, name) for a in t.args],
        )
    elif isinstance(t, LiquidHornApplication):
        if t.name == name:
            return rep
        else:
            return LiquidHornApplication(
                t.name,
                [(substitution_in_liquid(a, rep, name), t) for (a, t) in t.argtypes],
            )
    else:
        assert False


def substitution_in_type(t: Type, rep: Term, name: str) -> Type:
    """Substitutes name in type t with the new replacement term rep."""
    replacement: LiquidTerm | None = liquefy(rep)
    if replacement is None:
        return t

    def rec(t: Type) -> Type:
        return substitution_in_type(t, rep, name)

    renamed: Type

    if isinstance(t, Top):
        return t
    elif isinstance(t, Bottom):
        return t
    elif isinstance(t, BaseType):
        return t
    elif isinstance(t, TypeVar):
        return t
    elif isinstance(t, AbstractionType):
        if isinstance(rep, Var) and rep.name == t.var_name:
            nname = t.var_name + "1"
            renamed = AbstractionType(
                nname,
                t.var_type,
                substitution_in_type(t.type, Var(nname), t.var_name),
            )
            return substitution_in_type(renamed, rep, name)
        elif name == t.var_name:
            return t
        else:
            return AbstractionType(t.var_name, rec(t.var_type), rec(t.type))
    elif isinstance(t, RefinedType):
        if isinstance(rep, Var) and rep.name == t.name:
            nname = t.name + "1"
            renamed = RefinedType(
                nname,
                t.type,
                substitution_in_liquid(t.refinement, LiquidVar(nname), t.name),
            )
            return substitution_in_type(renamed, rep, name)
        elif t.name == name:
            return t
        else:
            return RefinedType(
                t.name,
                t.type,
                substitution_in_liquid(t.refinement, replacement, name),
            )
    assert False


def substitution(t: Term, rep: Term, name: str) -> Term:
    """Substitutes name in term t with the new replacement term rep."""

    def rec(x: Term):
        return substitution(x, rep, name)

    match t:
        case Literal(_):
            return t
        case Var(tname) | Hole(tname):
            if tname == name:
                return rep
            else:
                return t
        case Application(fun, arg):
            return Application(fun=rec(fun), arg=rec(arg))
        case Abstraction(vname, body):
            if vname == name:
                return t
            else:
                return Abstraction(vname, rec(t.body))
        case Let(tname, val, body):
            if tname == name:
                n_value = val
                n_body = body
            else:
                n_value = rec(val)
                n_body = rec(body)
            return Let(tname, n_value, n_body)
        case Rec(tname, ty, val, body):
            if tname == name:
                n_value = val
                n_body = body
            else:
                n_value = rec(val)
                n_body = rec(body)
            return Rec(tname, ty, n_value, n_body)
        case Annotation(body, ty):
            return Annotation(rec(body), ty)
        case If(cond, then, otherwise):
            return If(rec(cond), rec(then), rec(otherwise))
        case TypeApplication(expr, ty):
            return TypeApplication(rec(expr), ty)
        case _:
            assert False


def liquefy_app(app: Application) -> LiquidApp | None:
    arg = liquefy(app.arg)
    fun = app.fun
    while isinstance(fun, TypeApplication):
        fun = fun.body
    if not arg:
        return None
    if isinstance(fun, Var):
        return LiquidApp(fun.name, [arg])
    elif isinstance(fun, Application):
        liquid_pseudo_fun = liquefy_app(fun)
        if liquid_pseudo_fun:
            return LiquidApp(
                liquid_pseudo_fun.fun,
                liquid_pseudo_fun.args + [arg],
            )
        return None
    elif isinstance(fun, Let):
        return liquefy_app(
            Application(
                substitution(
                    fun.body,
                    fun.var_value,
                    fun.var_name,
                ),
                app.arg,
            ),
        )
    else:
        raise Exception(f"{app} is not a valid predicate.")


def liquefy_rec(t: Rec) -> LiquidTerm | None:
    value = liquefy(t.var_value)  # TODO: induction?
    body = liquefy(t.body)
    if value and body:
        return substitution_in_liquid(body, value, t.var_name)
    return None


def liquefy_let(t: Let) -> LiquidTerm | None:
    value = liquefy(t.var_value)
    body = liquefy(t.body)
    if value and body:
        return substitution_in_liquid(body, value, t.var_name)
    return None


def liquefy_if(t: If) -> LiquidTerm | None:
    co = liquefy(t.cond)
    th = liquefy(t.then)
    ot = liquefy(t.otherwise)
    if co and th and ot:
        return LiquidApp("ite", [co, th, ot])
    return None


def liquefy_ann(t: Annotation) -> LiquidTerm | None:
    return liquefy(t.expr)


# patterm matching term
def liquefy(rep: Term) -> LiquidTerm | None:
    if isinstance(rep, Literal) and rep.type == t_int:
        assert isinstance(rep.value, int)
        return LiquidLiteralInt(rep.value)
    elif isinstance(rep, Literal) and rep.type == t_float:
        assert isinstance(rep.value, float)
        return LiquidLiteralFloat(rep.value)
    elif isinstance(rep, Literal) and rep.type == t_bool:
        assert isinstance(rep.value, bool)
        return LiquidLiteralBool(rep.value)
    elif isinstance(rep, Literal) and rep.type == t_string:
        assert isinstance(rep.value, str)
        return LiquidLiteralString(rep.value)
    elif isinstance(rep, Application):
        return liquefy_app(rep)
    elif isinstance(rep, TypeApplication):
        return liquefy(rep.body)
    elif isinstance(rep, Var):
        return LiquidVar(rep.name)
    elif isinstance(rep, Hole):
        return LiquidHornApplication(rep.name, argtypes=[])
    elif isinstance(rep, Let):
        return liquefy_let(rep)
    elif isinstance(rep, Rec):
        return liquefy_rec(rep)
    elif isinstance(rep, If):
        return liquefy_if(rep)
    elif isinstance(rep, Annotation):
        return liquefy_ann(rep)
    raise Exception(f"Unable to liquefy {rep} {type(rep)}")
