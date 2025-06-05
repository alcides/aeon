from typing import MutableSequence
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
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Rec,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
    Literal,
)
from aeon.core.types import (
    AbstractionType,
    LiquidHornApplication,
    RefinedType,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
)
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    TypingContextEntry,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.utils.name import Name, fresh_counter


RenamingSubstitions = list[tuple[str, Name]]


def get_last_id(x: str, subs: RenamingSubstitions) -> Name | None:
    for sub, v in subs[::-1]:
        if x == sub:
            return v
    return None


def check_name(name: Name, subs: RenamingSubstitions) -> tuple[Name, RenamingSubstitions]:
    if name.id == -1:
        nname = Name(name.name, fresh_counter.fresh())
        return nname, subs + [(name.name, nname)]
    else:
        return name, subs + [(name.name, name)]


def apply_subs_name(subs: RenamingSubstitions, name: Name) -> Name:
    for sub, v in subs[::-1]:
        if sub == name.name:
            return v
    return name


def bind_lq(liq: LiquidTerm, subs: RenamingSubstitions) -> LiquidTerm:
    match liq:
        case LiquidLiteralBool(_) | LiquidLiteralInt(_) | LiquidLiteralFloat(_) | LiquidLiteralString(_):
            return liq
        case LiquidVar(name):
            return LiquidVar(apply_subs_name(subs, name))
        case LiquidApp(fun, args):
            nfun = apply_subs_name(subs, fun)
            return LiquidApp(nfun, [bind_lq(a, subs) for a in args])
        case LiquidHornApplication(name, argtyps):
            return LiquidHornApplication(apply_subs_name(subs, name), argtyps)
        case _:
            assert False, f"Constructed {liq} ({type(liq)}) not supported."


def bind_ctx(ctx: TypingContext, subs: RenamingSubstitions) -> tuple[TypingContext, RenamingSubstitions]:
    entries: MutableSequence[TypingContextEntry] = []
    subs = []
    for entry in ctx.entries:
        e: TypingContextEntry
        match entry:
            case VariableBinder(name, ty):
                name, subs = check_name(name, subs)
                e = VariableBinder(name, bind_type(ty, subs))
            case UninterpretedBinder(name, ty):
                name, subs = check_name(name, subs)
                nty = bind_type(ty, subs)
                assert isinstance(nty, AbstractionType)
                e = UninterpretedBinder(name, nty)
            case TypeBinder(name, k):
                name, subs = check_name(name, subs)
                e = TypeBinder(name, k)
            case TypeConstructorBinder(name, args):
                name, subs = check_name(name, subs)
                e = TypeConstructorBinder(name, args)
            case _:
                assert False, f"Unique not supported for {ctx} ({type(ctx)})"
        entries.append(e)
    return TypingContext(entries), subs


def bind_type(ty: Type, subs: RenamingSubstitions) -> Type:
    match ty:
        case Top():
            return Top()
        case TypeVar(name):
            return TypeVar(apply_subs_name(subs, name))
        case TypeConstructor(name, args):
            nargs = [bind_type(aty, subs) for aty in args]
            return TypeConstructor(apply_subs_name(subs, name), nargs)

        case AbstractionType(aname, atype, rtype):
            nname, nsubs = check_name(aname, subs)

            return AbstractionType(nname, bind_type(atype, subs), bind_type(rtype, nsubs))
        case RefinedType(name, ty, ref):
            nty = bind_type(ty, subs)
            nname, nsubs = check_name(name, subs)
            nref = bind_lq(ref, nsubs)
            assert isinstance(nty, TypeConstructor) or isinstance(nty, TypeVar) or isinstance(nty, TypeConstructor)
            return RefinedType(nname, nty, nref)
        case TypePolymorphism(name, kind, body):
            name, subs = check_name(name, subs)
            return TypePolymorphism(name, kind, bind_type(body, subs))
        case _:
            assert False, f"Unique not supported for {ty} ({type(ty)})"


def bind_term(t: Term, subs: RenamingSubstitions) -> Term:
    match t:
        case Literal(_, _):
            return t
        case Var(name):
            return Var(apply_subs_name(subs, name))
        case Hole(name):
            name, _ = check_name(name, subs)
            return Hole(name)
        case Annotation(e, ty):
            return Annotation(bind_term(e, subs), bind_type(ty, subs))
        case Application(e1, e2):
            return Application(bind_term(e1, subs), bind_term(e2, subs))
        case Abstraction(name, body):
            name, subs = check_name(name, subs)
            nbody = bind_term(body, subs)
            return Abstraction(name, nbody)
        case TypeApplication(body, ty):
            return TypeApplication(bind_term(body, subs), bind_type(ty, subs))
        case TypeAbstraction(name, kind, body):
            name, subs = check_name(name, subs)
            return TypeAbstraction(name, kind, bind_term(body, subs))
        case If(cond, then, otherwise):
            return If(bind_term(cond, subs), bind_term(then, subs), bind_term(otherwise, subs))
        case Let(name, body, cont):
            name, nsubs = check_name(name, subs)
            return Let(name, bind_term(body, subs), bind_term(cont, nsubs))
        case Rec(name, ty, body, cont):
            name, subs = check_name(name, subs)
            return Rec(name, bind_type(ty, subs), bind_term(body, subs), bind_term(cont, subs))
        case _:
            assert False, f"Unique not supported for {t} ({type(t)})"


def bind_ids(ctx: TypingContext, t: Term) -> tuple[TypingContext, Term]:
    ctx, subs = bind_ctx(ctx, [])
    return ctx, bind_term(t, subs)
