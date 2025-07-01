from typing import TypeVar
from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.terms import (
    Term,
    Literal,
    Var,
    Annotation,
    Hole,
    Application,
    Abstraction,
    Let,
    Rec,
    If,
    TypeAbstraction,
    TypeApplication,
)
from aeon.core.types import AbstractionType, RefinedType, Top, Type, TypeConstructor, TypePolymorphism
from aeon.sugar.program import (
    STerm,
    SLiteral,
    SVar,
    SAnnotation,
    SHole,
    SApplication,
    SAbstraction,
    SLet,
    SRec,
    SIf,
    STypeAbstraction,
    STypeApplication,
)
from aeon.sugar.stypes import SAbstractionType, SRefinedType, SType, STypeConstructor, STypePolymorphism, STypeVar
from aeon.sugar.ast_helpers import st_bool, st_int, st_float, st_string, st_top


def lift_liquid(ref: LiquidTerm) -> STerm:
    match ref:
        case LiquidLiteralBool(value, loc):
            return SLiteral(value, st_bool, loc)
        case LiquidLiteralInt(value, loc):
            return SLiteral(value, st_int, loc)
        case LiquidLiteralFloat(value, loc):
            return SLiteral(value, st_float, loc)
        case LiquidLiteralString(value, loc):
            return SLiteral(value, st_string, loc)
        case LiquidVar(name, loc):
            return SVar(name, loc)
        case LiquidApp(fun, args, loc):
            v: STerm = SVar(fun, loc=loc)
            for arg in args[::-1]:
                v = SApplication(v, lift_liquid(arg), loc=loc)
            return v
        case _:
            assert False, f"Don't know how to lift liquid term {ref} ({type(ref)})"


def lift_type(ty: Type) -> SType:
    match ty:
        case Top():
            return st_top
        case TypeVar(name, loc):
            return STypeVar(name, loc=loc)
        case TypeConstructor(name, args, loc):
            return STypeConstructor(name, [lift_type(arg) for arg in args], loc=loc)
        case AbstractionType(name, atype, rtype, loc):
            return SAbstractionType(name, lift_type(atype), lift_type(rtype), loc=loc)
        case RefinedType(name, typ, ref, loc):
            return SRefinedType(name, lift_type(typ), lift_liquid(ref), loc=loc)
        case TypePolymorphism(name, kind, body, loc):
            return STypePolymorphism(name, kind, lift_type(body), loc=loc)
        case _:
            assert False, f"Don't know how to lift type {ty} ({type(ty)})"


def lift(t: Term) -> STerm:
    match t:
        case Literal(value, typ, loc):
            # Convert core type to surface type (simple wrapper)
            return SLiteral(value, lift_type(typ), loc=loc)
        case Var(name, loc):
            return SVar(name, loc=loc)
        case Annotation(expr, typ, loc):
            return SAnnotation(lift(expr), lift_type(typ), loc=loc)
        case Hole(name, loc):
            return SHole(name, loc=loc)
        case Application(fun, arg, loc):
            return SApplication(lift(fun), lift(arg), loc=loc)
        case Abstraction(var_name, body, loc):
            return SAbstraction(var_name, lift(body), loc=loc)
        case Let(var_name, var_value, body, loc):
            return SLet(var_name, lift(var_value), lift(body), loc=loc)
        case Rec(var_name, var_type, var_value, body, loc):
            return SRec(var_name, lift_type(var_type), lift(var_value), lift(body), loc=loc)
        case If(cond, then, otherwise, loc):
            return SIf(lift(cond), lift(then), lift(otherwise), loc=loc)
        case TypeAbstraction(name, kind, body, loc):
            return STypeAbstraction(name, kind, lift(body), loc=loc)
        case TypeApplication(body, typ, loc):
            return STypeApplication(lift(body), lift_type(typ), loc=loc)
        case _:
            assert False, f"Don't know how to lift {t} ({type(t)})"
