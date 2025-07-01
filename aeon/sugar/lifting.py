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
        case LiquidLiteralBool(value):
            return SLiteral(value, st_bool)
        case LiquidLiteralInt(value):
            return SLiteral(value, st_int)
        case LiquidLiteralFloat(value):
            return SLiteral(value, st_float)
        case LiquidLiteralString(value):
            return SLiteral(value, st_string)
        case LiquidVar(name):
            return SVar(name)
        case LiquidApp(fun, args):
            v: STerm = SVar(fun)
            for arg in args[::-1]:
                v = SApplication(v, lift_liquid(arg))
            return v
        case _:
            assert False, f"Don't know how to lift liquid term {ref} ({type(ref)})"


def lift_type(ty: Type) -> SType:
    match ty:
        case Top():
            return st_top
        case TypeVar(name):
            return STypeVar(name)
        case TypeConstructor(name, args):
            return STypeConstructor(name, [lift_type(arg) for arg in args])
        case AbstractionType(name, atype, rtype):
            return SAbstractionType(name, lift_type(atype), lift_type(rtype))
        case RefinedType(name, typ, ref):
            return SRefinedType(name, lift_type(typ), lift_liquid(ref))
        case TypePolymorphism(name, kind, body):
            return STypePolymorphism(name, kind, lift_type(body))
        case _:
            assert False, f"Don't know how to lift type {ty} ({type(ty)})"


def lift(t: Term) -> STerm:
    match t:
        case Literal(value, typ):
            # Convert core type to surface type (simple wrapper)
            return SLiteral(value, lift_type(typ))
        case Var(name):
            return SVar(name)
        case Annotation(expr, typ):
            return SAnnotation(lift(expr), lift_type(typ))
        case Hole(name):
            return SHole(name)
        case Application(fun, arg):
            return SApplication(lift(fun), lift(arg))
        case Abstraction(var_name, body):
            return SAbstraction(var_name, lift(body))
        case Let(var_name, var_value, body):
            return SLet(var_name, lift(var_value), lift(body))
        case Rec(var_name, var_type, var_value, body):
            return SRec(var_name, lift_type(var_type), lift(var_value), lift(body))
        case If(cond, then, otherwise):
            return SIf(lift(cond), lift(then), lift(otherwise))
        case TypeAbstraction(name, kind, body):
            return STypeAbstraction(name, kind, lift(body))
        case TypeApplication(body, typ):
            return STypeApplication(lift(body), lift_type(typ))
        case _:
            assert False, f"Don't know how to lift {t} ({type(t)})"
