from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.types import LiquidHornApplication, RefinementPolymorphism, TypeConstructor, TypePolymorphism
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.terms import (
    Abstraction,
    RefinementAbstraction,
    RefinementApplication,
    TypeAbstraction,
    TypeApplication,
)
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
        case RefinedType(rname, ty, ref, loc):
            assert not isinstance(ty, RefinedType)
            return RefinedType(rname, rec(ty), ref, loc=loc)
        case AbstractionType(a, aty, rty, loc):
            return AbstractionType(a, rec(aty), rec(rty), loc=loc)
        case TypePolymorphism(pname, kind, body, loc):
            if name == pname:
                return t
            else:
                return TypePolymorphism(pname, kind, rec(body), loc=loc)
        case RefinementPolymorphism(rname, sort, body, loc):
            return RefinementPolymorphism(rname, rec(sort), rec(body), loc=loc)
        case TypeConstructor(cname, args, loc):
            return TypeConstructor(cname, [rec(arg) for arg in args], loc=loc)
        case _:
            assert False, f"type {t} ({type(t)}) not allows in substitution."


def substitute_vartype_in_term(t: Term, rep: Type, name: Name) -> Term:
    def rec(x: Term):
        return substitute_vartype_in_term(x, rep, name)

    match t:
        case Literal():
            return t
        case Var():
            return t
        case Hole():
            return t
        case Application(fun, arg, loc):
            return Application(fun=rec(fun), arg=rec(arg), loc=loc)
        case Abstraction(var_name, body, loc):
            return Abstraction(var_name, rec(body), loc=loc)
        case Let(var_name, var_value, body, loc):
            n_value = rec(var_value)
            n_body = rec(body)
            return Let(var_name, n_value, n_body, loc=loc)
        case Rec(var_name, var_type, var_value, body, decreasing_by, loc):
            n_value = rec(var_value)
            n_type = substitute_vartype(var_type, rep, name)
            n_body = rec(body)
            return Rec(var_name, n_type, n_value, n_body, decreasing_by=decreasing_by, loc=loc)
        case Annotation(expr, type, loc):
            n_type = substitute_vartype(type, rep, name)
            return Annotation(rec(expr), n_type, loc=loc)
        case If(cond, then, otherwise, loc):
            n_cond = rec(cond)
            n_then = rec(then)
            n_otherwise = rec(otherwise)
            return If(n_cond, n_then, n_otherwise, loc=loc)
        case TypeAbstraction(pname, kind, body, loc):
            return TypeAbstraction(pname, kind, rec(body), loc=loc)
        case TypeApplication(body, ty, loc):
            return TypeApplication(rec(body), substitute_vartype(ty, rep, name), loc=loc)
        case RefinementApplication(body, refinement, loc):
            return RefinementApplication(rec(body), rec(refinement), loc=loc)
        case RefinementAbstraction(pname, sort, body, loc):
            return RefinementAbstraction(pname, substitute_vartype(sort, rep, name), rec(body), loc=loc)
        case _:
            assert False


def instantiate_refinement_in_liquid(
    t: LiquidTerm,
    pred_name: Name,
    refinement: Abstraction,
) -> LiquidTerm:
    """Replaces LiquidApp(pred_name, [arg]) with the inlined refinement body.
    Implements tutorial fig 8.6: κ(x)[ρ := φ] = p[y := x] if ρ = κ:·, φ = λy.p"""
    match t:
        case LiquidApp(aname, args, loc):
            # TODO: support multi-arg predicates
            if aname == pred_name and len(args) == 1 and isinstance(args[0], LiquidVar):
                arg = args[0]
                body_subst = substitution(refinement.body, Var(arg.name, loc=arg.loc), refinement.var_name)
                body_subst = inline_lets(body_subst)
                liq = liquefy(body_subst)
                if liq is not None:
                    return liq
            return LiquidApp(
                aname,
                [instantiate_refinement_in_liquid(a, pred_name, refinement) for a in args],
                loc=loc,
            )
        case LiquidVar(_, loc):
            return t
        case (
            LiquidLiteralBool(_, loc)
            | LiquidLiteralInt(_, loc)
            | LiquidLiteralFloat(_, loc)
            | LiquidLiteralString(_, loc)
        ):
            return t
        case LiquidHornApplication(aname, argtypes, loc):
            return LiquidHornApplication(
                aname,
                [(instantiate_refinement_in_liquid(a, pred_name, refinement), ty) for (a, ty) in argtypes],
                loc=loc,
            )
        case _:
            assert False, f"Unknown LiquidTerm {t} ({type(t)})"


def instantiate_refinement_in_type(
    t: Type,
    pred_name: Name,
    refinement: Abstraction,
) -> Type:
    """Inlines the refinement predicate in the type.
    Implements s[ρ := φ] from tutorial fig 8.6.
    TODO: support refinement as Var ( id[Int]{myPred} ) — currently requires Abstraction."""
    match t:
        case Top() | TypeConstructor(_) | TypeVar(_):
            return t
        case AbstractionType(aname, atype, rtype, loc):
            return AbstractionType(
                aname,
                instantiate_refinement_in_type(atype, pred_name, refinement),
                instantiate_refinement_in_type(rtype, pred_name, refinement),
                loc=loc,
            )
        # b{ν:p}[ρ := φ] = b[ρ := φ]{ν:p[ρ := φ]} per tutorial fig 8.6
        case RefinedType(vname, ity, ref, loc):
            ntype = instantiate_refinement_in_type(ity, pred_name, refinement)
            assert isinstance(ntype, TypeConstructor) or isinstance(ntype, TypeVar)
            return RefinedType(
                vname,
                ntype,
                instantiate_refinement_in_liquid(ref, pred_name, refinement),
                loc=loc,
            )
        case TypePolymorphism(pname, kind, body, loc):
            return TypePolymorphism(pname, kind, instantiate_refinement_in_type(body, pred_name, refinement), loc=loc)
        case RefinementPolymorphism(rname, rsort, rbody, loc):
            return RefinementPolymorphism(
                rname,
                instantiate_refinement_in_type(rsort, pred_name, refinement),
                instantiate_refinement_in_type(rbody, pred_name, refinement),
                loc=loc,
            )
        case TypeConstructor(name, args, loc):
            return TypeConstructor(
                name, [instantiate_refinement_in_type(arg, pred_name, refinement) for arg in args], loc=loc
            )
        case _:
            assert False, f"Unknown type {t} ({type(t)})"


def instantiate_refinement_with_horn_in_liquid(
    t: LiquidTerm,
    pred_name: Name,
    sort: Type,
    horn_name: Name,
) -> LiquidTerm:
    """Replace LiquidApp(ρ, args) with LiquidHornApplication(horn_name, ...) for implicit Syn-RApp."""

    def rec(lt: LiquidTerm) -> LiquidTerm:
        return instantiate_refinement_with_horn_in_liquid(lt, pred_name, sort, horn_name)

    match t:
        case LiquidVar(_):
            return t
        case LiquidLiteralBool(_) | LiquidLiteralInt(_) | LiquidLiteralFloat(_) | LiquidLiteralString(_):
            return t
        case LiquidApp(aname, args, loc):
            if aname == pred_name:
                assert isinstance(sort, TypeConstructor) or isinstance(sort, TypeVar)
                return LiquidHornApplication(horn_name, [(a, sort) for a in args], loc=loc)
            return LiquidApp(aname, [rec(a) for a in args], loc=loc)
        case LiquidHornApplication(aname, argtypes, loc):
            return LiquidHornApplication(
                aname,
                [(rec(a), ty) for (a, ty) in argtypes],
                loc=loc,
            )
        case _:
            assert False, f"instantiate_refinement_with_horn_in_liquid: unknown liquid {t}"


def instantiate_refinement_with_horn_in_type(
    t: Type,
    pred_name: Name,
    sort: Type,
    horn_name: Name,
) -> Type:
    """Walk types and apply instantiate_refinement_with_horn_in_liquid in refinements."""

    def rec(ty: Type) -> Type:
        return instantiate_refinement_with_horn_in_type(ty, pred_name, sort, horn_name)

    match t:
        case Top():
            return t
        case TypeVar(_):
            return t
        case TypeConstructor(name, args, loc):
            return TypeConstructor(name, [rec(a) for a in args], loc=loc)
        case AbstractionType(aname, atype, rtype, loc):
            return AbstractionType(aname, rec(atype), rec(rtype), loc=loc)
        case RefinedType(vname, ity, ref, loc):
            nity = rec(ity)
            assert isinstance(nity, TypeConstructor) or isinstance(nity, TypeVar)
            return RefinedType(
                vname,
                nity,
                instantiate_refinement_with_horn_in_liquid(ref, pred_name, sort, horn_name),
                loc=loc,
            )
        case TypePolymorphism(pname, kind, body, loc):
            return TypePolymorphism(pname, kind, rec(body), loc=loc)
        case RefinementPolymorphism(rname, rsort, rbody, loc):
            return RefinementPolymorphism(rname, rec(rsort), rec(rbody), loc=loc)
        case _:
            assert False, f"instantiate_refinement_with_horn_in_type: unknown type {t}"


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
        case LiquidApp(aname, args, loc):
            if aname == name:
                assert isinstance(rep, LiquidVar)
                nname = rep.name
            else:
                nname = aname
            return LiquidApp(nname, [substitution_in_liquid(a, rep, name) for a in args], loc=loc)

        case LiquidHornApplication(aname, argtypes, loc):
            if aname == name:
                assert isinstance(rep, LiquidVar)
                nname = rep.name
            else:
                nname = aname
            return LiquidHornApplication(
                aname, [(substitution_in_liquid(a, rep, name), t) for (a, t) in argtypes], loc=loc
            )
        case _:
            assert False, f"{t} ({type(t)}) not allowed in substitution."


def substitution_liquid_in_type(t: Type, rep: LiquidTerm, name: Name) -> Type:
    def rec(t: Type) -> Type:
        return substitution_liquid_in_type(t, rep, name)

    match t:
        case Top() | TypeConstructor(_) | TypeVar(_):
            return t
        case AbstractionType(aname, atype, rtype, loc):
            if aname == name:
                return t
            else:
                return AbstractionType(aname, rec(atype), rec(rtype), loc=loc)
        case RefinedType(vname, ity, ref, loc):
            if name == vname:
                return t
            else:
                return RefinedType(vname, ity, substitution_in_liquid(ref, rep, name), loc=loc)
        case TypePolymorphism(name, kind, body, loc):
            return TypePolymorphism(name, kind, rec(body), loc=loc)
        case RefinementPolymorphism(rname, rsort, rbody, loc):
            if rname == name:
                return t
            return RefinementPolymorphism(rname, rec(rsort), rec(rbody), loc=loc)
        case TypeConstructor(name, args, loc):
            return TypeConstructor(name, [rec(arg) for arg in args], loc=loc)
        case _:
            assert False, f"{t} not allowed"


def substitution_liquid_in_term(t: Term, rep: LiquidTerm, name: Name) -> Term:
    def rec(x: Term) -> Term:
        return substitution_liquid_in_term(x, rep, name)

    match t:
        case Literal(val, ty, loc):
            return Literal(val, substitution_liquid_in_type(ty, rep, name), loc=loc)
        case Var():
            return t
        case Hole():
            return t
        case Application(fun, arg, loc):
            return Application(fun=rec(fun), arg=rec(arg), loc=loc)
        case Abstraction(var_name, body, loc):
            return Abstraction(var_name, rec(body), loc=loc)
        case Let(var_name, var_value, body, loc):
            return Let(var_name, rec(var_value), rec(body), loc=loc)
        case Rec(var_name, var_type, var_value, body, decreasing_by, loc):
            n_type = substitution_liquid_in_type(var_type, rep, name)
            return Rec(var_name, n_type, rec(var_value), rec(body), decreasing_by=decreasing_by, loc=loc)
        case Annotation(expr, ty, loc):
            n_type = substitution_liquid_in_type(ty, rep, name)
            return Annotation(rec(expr), n_type, loc=loc)
        case If(cond, then, otherwise, loc):
            return If(rec(cond), rec(then), rec(otherwise), loc=loc)
        case TypeAbstraction(pname, kind, body, loc):
            return TypeAbstraction(pname, kind, rec(body), loc=loc)
        case RefinementAbstraction(pname, sort, body, loc):
            return RefinementAbstraction(pname, substitution_liquid_in_type(sort, rep, name), rec(body), loc=loc)
        case TypeApplication(body, ty, loc):
            n_type = substitution_liquid_in_type(ty, rep, name)
            return TypeApplication(rec(body), n_type, loc=loc)
        case RefinementApplication(body, refinement, loc):
            return RefinementApplication(rec(body), rec(refinement), loc=loc)
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
        case AbstractionType(aname, atype, rtype, loc):
            if aname == name:
                return t
            else:
                return AbstractionType(aname, rec(atype), rec(rtype), loc=loc)
        case RefinedType(vname, ity, ref, loc):
            if name == vname:
                return t
            else:
                return RefinedType(vname, ity, substitution_in_liquid(ref, replacement, name), loc=loc)
        case TypePolymorphism(name, kind, body, loc):
            return TypePolymorphism(name, kind, rec(body), loc=loc)
        case TypeConstructor(name, args, loc):
            return TypeConstructor(name, [rec(arg) for arg in args], loc=loc)
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
        case Application(fun, arg, loc):
            return Application(fun=rec(fun), arg=rec(arg), loc=loc)
        case Abstraction(vname, body, loc):
            if vname == name:
                return t
            else:
                return Abstraction(vname, rec(t.body), loc=loc)
        case Let(tname, val, body, loc):
            if tname == name:
                n_value = val
                n_body = body
            else:
                n_value = rec(val)
                n_body = rec(body)
            return Let(tname, n_value, n_body, loc=loc)
        case Rec(tname, ty, val, body, decreasing_by, loc):
            if tname == name:
                n_value = val
                n_body = body
            else:
                n_value = rec(val)
                n_body = rec(body)
            return Rec(tname, ty, n_value, n_body, decreasing_by=decreasing_by, loc=loc)
        case Annotation(body, ty, loc):
            return Annotation(rec(body), ty, loc=loc)
        case If(cond, then, otherwise, loc):
            return If(rec(cond), rec(then), rec(otherwise), loc=loc)
        case TypeApplication(expr, ty, loc):
            return TypeApplication(rec(expr), ty, loc=loc)
        case TypeAbstraction(pname, kind, body, loc):
            return TypeAbstraction(pname, kind, rec(body), loc=loc)
        case RefinementAbstraction(pname, sort, body, loc):
            return RefinementAbstraction(pname, sort, rec(body), loc=loc)
        case RefinementApplication(body, refinement, loc):
            return RefinementApplication(rec(body), rec(refinement), loc=loc)
        case _:
            assert False, f"{t} not supported."


def inline_lets(t: Term) -> Term:
    """Inlines all lets in the term t."""
    match t:
        case Let(var_name, var_value, body):
            return inline_lets(substitution(body, var_value, var_name))
        case Rec(var_name, _, var_value, body, _, _):
            return inline_lets(substitution(body, var_value, var_name))
        case Application(Annotation(Abstraction(var_name, body), _), arg):
            return inline_lets(substitution(body, arg, var_name))
        case Application(Abstraction(var_name, body), arg):
            return inline_lets(substitution(body, arg, var_name))
        case Application(fun, arg, loc):
            return Application(inline_lets(fun), inline_lets(arg), loc=loc)
        case Abstraction(var_name, body, loc):
            return Abstraction(var_name, inline_lets(body), loc=loc)
        case If(cond, then, otherwise, loc):
            return If(inline_lets(cond), inline_lets(then), inline_lets(otherwise), loc=loc)
        case TypeApplication(TypeAbstraction(name, _, body), ty, loc):
            return inline_lets(substitute_vartype_in_term(body, ty, name))
        case TypeApplication(expr, ty, loc):
            return TypeApplication(inline_lets(expr), ty, loc=loc)
        case _:
            return t


def uncurry(t: Term, args: list[LiquidTerm]) -> LiquidTerm | None:
    """Uncurries the term t."""
    match t:
        case TypeApplication(body, _):
            return uncurry(body, args)
        case RefinementApplication(body, _):
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
                case LiquidVar(name, loc):
                    return LiquidApp(name, args, loc=loc)
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
        return LiquidApp(Name("ite", 0), [co, th, ot], loc=t.loc)
    return None


def liquefy_ann(t: Annotation) -> LiquidTerm | None:
    return liquefy(t.expr)


# patterm matching term
def liquefy(rep: Term) -> LiquidTerm | None:
    """Converts a term to a liquid term."""

    rep = inline_lets(rep)

    assert isinstance(rep, Term), "not term"
    match rep:
        case Literal(val, TypeConstructor(Name("Int", 0)), loc):
            assert isinstance(val, int)
            return LiquidLiteralInt(val, loc=loc)
        case Literal(val, TypeConstructor(Name("Float", 0)), loc):
            assert isinstance(val, float)
            return LiquidLiteralFloat(val, loc=loc)
        case Literal(val, TypeConstructor(Name("Bool", 0)), loc):
            assert isinstance(val, bool)
            return LiquidLiteralBool(val, loc=loc)
        case Literal(val, TypeConstructor(Name("String", 0)), loc):
            assert isinstance(val, str)
            return LiquidLiteralString(val, loc=loc)
        case Application(_, _):
            return liquefy_app(rep)
        case TypeAbstraction(_, _, body):
            return liquefy(body)
        case RefinementAbstraction(_, _, body):
            return liquefy(body)
        case Var(name, loc):
            return LiquidVar(name, loc=loc)
        case Hole(name, loc):
            return LiquidHornApplication(name, argtypes=[], loc=loc)
        case Let(_, _, _):
            return liquefy_let(rep)
        case Rec(_, _, _, _, _):
            return liquefy_rec(rep)
        case If(_, _, _):
            return liquefy_if(rep)
        case Annotation(_, _):
            return liquefy_ann(rep)
        case TypeApplication(body, _):
            return liquefy(body)
        case RefinementApplication(body, _):
            return liquefy(body)
        case Abstraction(_, _):
            return None
        case _:
            raise Exception(f"Unable to liquefy {rep} {type(rep)}")
