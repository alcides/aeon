from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.types import LiquidHornApplication, TypeConstructor, TypePolymorphism
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
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
from aeon.core.types import AbstractionType
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypeVar
from aeon.utils.name import Name


def substitute_vartype(t: Type, rep: Type, name: Name) -> Type:
    """Replaces all occurrences of vartypes name in t by rep."""

    def rec(k: Type):
        return substitute_vartype(k, rep, name)

    match t:
        case TypeVar(tname):
            if tname == name:
                return rep
            else:
                return t
        case RefinedType(rname, ty, ref):
            assert not isinstance(ty, RefinedType)
            return RefinedType(rname, rec(ty), ref)
        case AbstractionType(a, aty, rty):
            return AbstractionType(a, rec(aty), rec(rty))
        case TypePolymorphism(pname, kind, body):
            if name == pname:
                return t
            else:
                return TypePolymorphism(pname, kind, rec(body))
        case TypeConstructor(cname, args):
            return TypeConstructor(cname, [rec(arg) for arg in args])
        case _:
            assert False, f"type {t} ({type(t)}) not allows in substitution."


def substitute_vartype_in_term(t: Term, rep: Type, name: Name) -> Term:
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
    name: Name,
) -> LiquidTerm:
    """substitutes name in the term t with the new replacement term rep."""
    match t:
        case LiquidLiteralBool(_) | LiquidLiteralInt(_) | LiquidLiteralFloat(_) | LiquidLiteralString(_):
            return t
        case LiquidVar(tname):
            if tname == name:
                return rep
            else:
                return t
        case LiquidApp(aname, args):
            if aname == name:
                assert isinstance(rep, LiquidVar)
                nname = rep.name
            else:
                nname = aname
            return LiquidApp(nname, [substitution_in_liquid(a, rep, name) for a in args])

        case LiquidHornApplication(aname, argtypes):
            if aname == name:
                assert isinstance(rep, LiquidVar)
                nname = rep.name
            else:
                nname = aname
            return LiquidHornApplication(aname, [(substitution_in_liquid(a, rep, name), t) for (a, t) in argtypes])
        case _:
            assert False, f"{t} ({type(t)}) not allowed in substitution."


def substitution_liquid_in_type(t: Type, rep: LiquidTerm, name: Name) -> Type:
    def rec(t: Type) -> Type:
        return substitution_liquid_in_type(t, rep, name)

    match t:
        case Top() | TypeConstructor(_) | TypeVar(_):
            return t
        case AbstractionType(aname, atype, rtype):
            if aname == name:
                return t
            else:
                return AbstractionType(aname, rec(atype), rec(rtype))
        case RefinedType(vname, ity, ref):
            if name == vname:
                return t
            else:
                return RefinedType(
                    vname,
                    ity,
                    substitution_in_liquid(ref, rep, name),
                )
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(name, kind, rec(body))
        case TypeConstructor(name, args):
            return TypeConstructor(name, [rec(arg) for arg in args])
        case _:
            assert False, f"{t} not allowed"


def substitution_in_type(t: Type, rep: Term, name: Name) -> Type:
    """Substitutes name in type t with the new replacement term rep."""
    replacement: LiquidTerm | None = liquefy(rep)
    if replacement is None:
        return t

    def rec(t: Type) -> Type:
        return substitution_in_type(t, rep, name)

    match t:
        case Top() | TypeConstructor(_) | TypeVar(_):
            return t
        case AbstractionType(aname, atype, rtype):
            if aname == name:
                return t
            else:
                return AbstractionType(aname, rec(atype), rec(rtype))
        case RefinedType(vname, ity, ref):
            if name == vname:
                return t
            else:
                return RefinedType(
                    vname,
                    ity,
                    substitution_in_liquid(ref, replacement, name),
                )
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(name, kind, rec(body))
        case TypeConstructor(name, args):
            return TypeConstructor(name, [rec(arg) for arg in args])
        case _:
            assert False, f"{t} not allowed"


def substitution(t: Term, rep: Term, name: Name) -> Term:
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
        case TypeAbstraction(pname, kind, body):
            return TypeAbstraction(pname, kind, rec(body))
        case _:
            assert False, f"{t} not supported."


def inline_lets(t: Term) -> Term:
    """Inlines all lets in the term t."""
    match t:
        case Let(var_name, var_value, body):
            return inline_lets(substitution(body, var_value, var_name))
        case Rec(var_name, _, var_value, body):
            return inline_lets(substitution(body, var_value, var_name))
        case Application(Annotation(Abstraction(var_name, body), _), arg):
            return inline_lets(substitution(body, arg, var_name))
        case Application(Abstraction(var_name, body), arg):
            return inline_lets(substitution(body, arg, var_name))
        case Application(fun, arg):
            return Application(inline_lets(fun), inline_lets(arg))
        case Abstraction(var_name, body):
            return Abstraction(var_name, inline_lets(body))
        case If(cond, then, otherwise):
            return If(inline_lets(cond), inline_lets(then), inline_lets(otherwise))
        case TypeApplication(TypeAbstraction(name, _, body), ty):
            return inline_lets(substitute_vartype_in_term(body, ty, name))
        case TypeApplication(expr, ty):
            return TypeApplication(inline_lets(expr), ty)
        case _:
            return t


def uncurry(t: Term, args: list[LiquidTerm]) -> LiquidTerm | None:
    """Uncurries the term t."""
    match t:
        case TypeApplication(body, _):
            return uncurry(body, args)
        case Application(fun, arg):
            liquid_arg = liquefy(arg)
            if liquid_arg is None:
                return None
            else:
                return uncurry(fun, [liquid_arg] + args)
        case _:
            liquid_t = liquefy(t)
            match liquid_t:
                case None:
                    return None
                case LiquidVar(name):
                    return LiquidApp(name, args)
                case _:
                    assert False, f"Unknown term {t} {type(t)} in uncurry: {liquid_t}"


def liquefy_app(app: Application) -> LiquidApp | None:
    assert isinstance(app, Application), "not application"
    lapp = uncurry(app, [])
    assert isinstance(lapp, LiquidApp) or lapp is None
    return lapp


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
        return LiquidApp(Name("ite", 0), [co, th, ot])
    return None


def liquefy_ann(t: Annotation) -> LiquidTerm | None:
    return liquefy(t.expr)


# patterm matching term
def liquefy(rep: Term) -> LiquidTerm | None:
    """Converts a term to a liquid term."""

    rep = inline_lets(rep)

    assert isinstance(rep, Term), "not term"
    match rep:
        case Literal(val, TypeConstructor(Name("Int", 0))):
            assert isinstance(val, int)
            return LiquidLiteralInt(val)
        case Literal(val, TypeConstructor(Name("Float", 0))):
            assert isinstance(val, float)
            return LiquidLiteralFloat(val)
        case Literal(val, TypeConstructor(Name("Bool", 0))):
            assert isinstance(val, bool)
            return LiquidLiteralBool(val)
        case Literal(val, TypeConstructor(Name("String", 0))):
            assert isinstance(val, str)
            return LiquidLiteralString(val)
        case Application(_, _):
            return liquefy_app(rep)
        case TypeAbstraction(_, _, body):
            return liquefy(body)
        case Var(name):
            return LiquidVar(name)
        case Hole(name):
            return LiquidHornApplication(name, argtypes=[])
        case Let(_, _, _):
            return liquefy_let(rep)
        case Rec(_, _, _, _):
            return liquefy_rec(rep)
        case If(_, _, _):
            return liquefy_if(rep)
        case Annotation(_, _):
            return liquefy_ann(rep)
        case Abstraction(_, _):
            return None
        case _:
            raise Exception(f"Unable to liquefy {rep} {type(rep)}")
