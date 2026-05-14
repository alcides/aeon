"""Core substitution and instantiation walks.

The pure recursive walks live in the Rust core (aeon_rs):
- substitute_vartype / substitute_vartype_in_term
- substitution_in_liquid / substitution_liquid_in_type / substitution_liquid_in_term
- instantiate_refinement_with_horn_in_liquid / _in_type
- substitution (term-level)

The mutually-recursive cluster (inline_lets / liquefy / liquefy_* /
substitution_in_type / instantiate_refinement_in_{liquid,type}) stays in
Python — they depend on each other in a tight cycle that's better moved
together in a follow-up PR.
"""

from __future__ import annotations

from aeon_rs import instantiate_refinement_with_horn_in_liquid as instantiate_refinement_with_horn_in_liquid
from aeon_rs import instantiate_refinement_with_horn_in_type as instantiate_refinement_with_horn_in_type
from aeon_rs import substitute_vartype as substitute_vartype
from aeon_rs import substitute_vartype_in_term as substitute_vartype_in_term
from aeon_rs import substitution as substitution
from aeon_rs import substitution_in_liquid as substitution_in_liquid
from aeon_rs import substitution_liquid_in_term as substitution_liquid_in_term
from aeon_rs import substitution_liquid_in_type as substitution_liquid_in_type

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    LiquidHornApplication,
    RefinedType,
    RefinementPolymorphism,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
)
from aeon.utils.name import Name


def instantiate_refinement_in_liquid(
    t: LiquidTerm,
    pred_name: Name,
    refinement: Abstraction,
) -> LiquidTerm:
    """Replaces LiquidApp(pred_name, [arg]) with the inlined refinement body.

    Implements tutorial fig 8.6: κ(x)[ρ := φ] = p[y := x] if ρ = κ:·, φ = λy.p
    """
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
    TODO: support refinement as Var ( id[Int]{myPred} ) — currently requires Abstraction.
    """
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


# pattern matching term
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
