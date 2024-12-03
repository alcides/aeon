from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralFloat
from aeon.core.liquid import LiquidHornApplication
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.terms import Abstraction, TypeAbstraction, TypeApplication
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, TypeConstructor, TypePolymorphism
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

    match t:
        case Bottom():
            return t
        case Top():
            return t
        case BaseType(_):
            return t
        case TypeVar(name=n):
            if n == name:
                return rep
            else:
                return t
        case RefinedType(name=n, type=ty, refinement=ref):
            it = RefinedType(n, rec(ty), ref)
            while isinstance(it.type, RefinedType):
                nr = substitution_in_liquid(it.type.refinement,
                                            LiquidVar(t.name), it.type.name)
                ncond = LiquidApp("&&", [t.refinement, nr])
                it = RefinedType(t.name, it.type.type, ncond)
            return it
        case AbstractionType(var_name=n, var_type=vty, type=ty):
            return AbstractionType(n, rec(vty), rec(ty))
        case TypePolymorphism(name=n, kind=k, body=ty):
            if n == name:  # Avoid incorrect alpha renaming
                return t
            else:
                return TypePolymorphism(n, k, rec(ty))
        case TypeConstructor(name=n, args=args):
            return TypeConstructor(name=n, args=[rec(a) for a in args])
        case _:
            assert False


def substitute_vartype_in_term(t: Term, rep: Type, name: str):

    def rec(x: Term):
        return substitute_vartype_in_term(x, rep, name)

    match t:
        case Literal(_):
            return t
        case Var(_):
            return t
        case Hole(_):
            return t
        case Application(fun=fun, arg=arg):
            return Application(fun=rec(fun), arg=rec(arg))
        case Abstraction(var_name=n, body=b):
            return Abstraction(var_name=n, body=rec(b))
        case Let(var_name=n, var_value=v, body=b):
            return Let(n, rec(v), rec(b))
        case Rec(var_name=n, var_type=ty, var_value=v, body=b):
            return Rec(n, substitute_vartype(ty, rep, name), rec(v), rec(b))
        case Annotation(expr=e, type=ty):
            return Annotation(rec(e), substitute_vartype(ty, rep, name))
        case If(cond=cond, then=then, otherwise=otherwise):
            return If(rec(cond), rec(then), rec(otherwise))
        case TypeApplication(body=e, type=ty):
            return TypeApplication(rec(e), substitute_vartype(ty, rep, name))
        case TypeAbstraction(name=n, kind=k, body=e):
            return TypeAbstraction(n, k, rec(e))
        case _:
            assert False


def substitution_in_liquid(t: LiquidTerm, rep: LiquidTerm,
                           name: str) -> LiquidTerm:
    """Substitutes name in the term t with the new replacement term rep."""
    assert isinstance(rep, LiquidTerm)
    match t:
        case LiquidLiteralInt(value=_):
            return t
        case LiquidLiteralBool(value=_):
            return t
        case LiquidLiteralFloat(value=_):
            return t
        case LiquidLiteralString(value=_):
            return t
        case LiquidVar(name=n):
            if n == name:
                return rep
            else:
                return t
        case LiquidApp(fun=fun, args=args):
            if fun == name and isinstance(rep, LiquidVar):
                nfun = rep.name
            else:
                nfun = fun
            return LiquidApp(
                nfun, [substitution_in_liquid(a, rep, name) for a in args])
        case LiquidHornApplication(n, argtypes):
            if n == name:
                return rep
            else:
                return LiquidHornApplication(
                    n,
                    [(substitution_in_liquid(a, rep, name), t)
                     for (a, t) in argtypes],
                )
        case _:
            assert False, f"{t} is not a supported type."


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
    elif isinstance(t, TypeConstructor):
        return TypeConstructor(t.name, [rec(a) for a in t.args])
    else:
        assert False, f"Could not handle {t} in substition ({type(t)})"


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
            ), )
    else:
        raise Exception(f"{app} is not a valid predicate.")


def liquefy_rec(t: Rec) -> LiquidTerm | None:
    value = liquefy(t.var_value)  # TODO
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
    match rep:
        case Literal(value=_, type=ty):
            if ty == t_int:
                assert isinstance(rep.value, int)
                return LiquidLiteralInt(rep.value)
            elif ty == t_bool:
                assert isinstance(rep.value, bool)
                return LiquidLiteralBool(rep.value)
            elif ty == t_float:
                assert isinstance(rep.value, float)
                return LiquidLiteralFloat(rep.value)
            elif ty == t_string:
                assert isinstance(rep.value, str)
                return LiquidLiteralString(rep.value)
            else:
                assert False, "Literal {rep} has a type {ty} that is not supported."
        case Var(name=n):
            return LiquidVar(n)
        case Hole(name=n):
            return LiquidHornApplication(n)
        case Annotation(expr=e, type=_):
            return liquefy_ann(rep)
        case Application(fun=_, arg=_):
            return liquefy_app(rep)
        case Let(var_name=_, var_value=_, body=_):
            return liquefy_let(rep)
        case Rec(var_name=_, var_type=_, var_value=_, body=_):
            return liquefy_rec(rep)
        case If(cond=_, then=_, otherwise=_):
            return liquefy_if(rep)
        case TypeApplication(body=e, type=ty):
            return liquefy(e)
        case TypeAbstraction(name=_, kind=_, body=e):
            return liquefy(e)
        case _:
            raise Exception(f"Unable to liquefy {rep} {type(rep)}")
