from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution, substitution_in_liquid, substitution_in_type
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
    BaseType,
    RefinedType,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
)
from aeon.typechecking.context import (
    EmptyContext,
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)


def unique_ids(ctx: TypingContext, t: Term) -> tuple[TypingContext, Term]:
    counter = 0

    def get_name(old_name: str) -> str:
        nonlocal counter
        counter += 1
        return f"{old_name}_{counter}"

    def unique_ctx(ctx: TypingContext) -> TypingContext:
        match ctx:
            case EmptyContext():
                return ctx
            case VariableBinder(prev, name, ty):
                return VariableBinder(unique_ctx(prev), name, unique_type(ty))
            case UninterpretedBinder(prev, name, ty):
                nty = unique_type(ty)
                assert isinstance(nty, AbstractionType)
                return UninterpretedBinder(unique_ctx(prev), name, nty)
            case TypeBinder(prev, name, kind):
                return TypeBinder(unique_ctx(prev), name, kind)
            case TypeConstructorBinder(prev, name, args):
                return TypeConstructorBinder(unique_ctx(prev), name, args)
            case _:
                assert False, f"Unique not supported for {ctx} ({type(ctx)})"

    def unique_type(ty: Type) -> Type:
        match ty:
            case BaseType(_) | Top() | TypeVar(_) | TypeConstructor(_, _):
                return ty
            case AbstractionType(aname, atype, rtype):
                nname = get_name(aname)
                nrtype = substitution_in_type(rtype, Var(nname), aname)
                return AbstractionType(nname, unique_type(atype),
                                       unique_type(nrtype))
            case RefinedType(name, ty, ref):
                nname = get_name(name)
                nref = substitution_in_liquid(ref, LiquidVar(nname), name)
                nty = unique_type(ty)
                assert isinstance(nty, BaseType) or isinstance(
                    nty, TypeVar) or isinstance(nty, TypeConstructor)
                return RefinedType(nname, nty, nref)
            case TypePolymorphism(name, kind, body):
                return TypePolymorphism(name, kind, unique_type(body))
            case _:
                assert False, f"Unique not supported for {ty} ({type(ty)})"

    def unique_term(t: Term) -> Term:
        match t:
            case Literal(_, _) | Var(_) | Hole(_):
                return t
            case Annotation(e, ty):
                return Annotation(unique_term(e), unique_type(ty))
            case Application(e1, e2):
                return Application(unique_term(e1), unique_term(e2))
            case Abstraction(name, body):
                nname = get_name(name)
                nbody = substitution(body, Var(nname), name)
                return Abstraction(nname, nbody)
            case TypeApplication(body, ty):
                return TypeApplication(unique_term(body), unique_type(ty))
            case TypeAbstraction(name, kind, body):
                return TypeAbstraction(name, kind, unique_term(body))
            case If(cond, then, otherwise):
                return If(unique_term(cond), unique_term(then),
                          unique_term(otherwise))
            case Let(name, body, cont):
                # nname = get_name(name)
                # ncont = substitution(cont, Var(nname), name)
                return Let(name, body, cont)
            case Rec(name, ty, body, cont):
                # nname = get_name(name)
                # nbody = substitution(body, Var(nname), name)
                # ncont = substitution(cont, Var(nname), name)
                return Rec(name, unique_type(ty), body, cont)
            case _:
                assert False, f"Unique not supported for {t} ({type(t)})"

    return unique_ctx(ctx), unique_term(t)
