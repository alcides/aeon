from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.types import LiquidHornApplication, TypeConstructor
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    If,
    Let,
    Literal,
    Rec,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
    Hole,
)
from aeon.core.types import AbstractionType, BaseType, RefinedType, Type, TypePolymorphism, Top, TypeVar
from aeon.elaboration.context import (
    ElabTypeDecl,
    ElabTypeVarBinder,
    ElabUninterpretedBinder,
    ElabVariableBinder,
    ElaborationTypingContext,
)
from aeon.sugar.program import (
    SAbstraction,
    SAnnotation,
    SApplication,
    SIf,
    SLet,
    SLiteral,
    SRec,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
    SHole,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SBaseType,
    SRefinedType,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
)
from aeon.sugar.substitutions import normalize, substitution_sterm_in_sterm, substitution_sterm_in_stype
from aeon.typechecking.context import (
    EmptyContext,
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)


class LoweringException(Exception):
    pass


class LiquefactionException(LoweringException):
    pass


# TODO: NOW! detect built-in SMT functions
def liquefy_app(app: SApplication) -> LiquidApp | None:
    arg = liquefy(app.arg)
    fun = app.fun
    while isinstance(fun, STypeApplication):
        fun = fun.body
    if not arg:
        return None

    match fun:
        case SVar(name):
            return LiquidApp(name, [arg])
        case SApplication(_, _):
            liquid_pseudo_fun = liquefy_app(fun)
            if liquid_pseudo_fun:
                return LiquidApp(
                    liquid_pseudo_fun.fun,
                    liquid_pseudo_fun.args + [arg],
                )
            return None
        case SLet(name, val, body):
            app = SApplication(substitution_sterm_in_sterm(body, val, name),
                               app.arg)
            return liquefy_app(app)
        case _:
            raise LiquefactionException(f"{app} is not a valid predicate.")


def liquefy(
    t: STerm,
    available_vars: list[tuple[str, BaseType | TypeVar | TypeConstructor]]
    | None = None
) -> LiquidTerm:
    """Converts Surface Terms into Liquid Terms"""
    match t:
        case SLiteral(val, SBaseType("Bool")):
            assert isinstance(val, bool)
            return LiquidLiteralBool(val)
        case SLiteral(val, SBaseType("Int")):
            assert isinstance(val, int)
            return LiquidLiteralInt(val)
        case SLiteral(val, SBaseType("Float")):
            assert isinstance(val, float)
            return LiquidLiteralFloat(val)
        case SLiteral(val, SBaseType("String")):
            assert isinstance(val, str)
            return LiquidLiteralString(val)
        case SLiteral(_, _):
            assert False, f"{t} is not convertable to liquid term."
        case SVar(name):
            return LiquidVar(name)
        case SIf(cond, then, otherwise):
            co = liquefy(cond, available_vars)
            th = liquefy(then, available_vars)
            ot = liquefy(otherwise, available_vars)
            if co is not None and th is not None and ot is not None:
                return LiquidApp("ite", [co, th, ot])
            return None
        case SAnnotation(expr, _):
            return liquefy(expr, available_vars)
        case SAbstraction(name, body):
            return None
        case STypeApplication(expr, _):
            return liquefy(expr, available_vars)
        case STypeAbstraction(name, _, body):
            return liquefy(body, available_vars)
        case SApplication(_, _):
            return liquefy_app(t)
        case SLet(name, val, body):
            lval = liquefy(val, available_vars)
            lbody = liquefy(body, available_vars)
            if lval and lbody:
                return substitution_in_liquid(lbody, lval, name)
            return None
        case SRec(name, _, val, body):
            lval = liquefy(val, available_vars)  # TODO: induction?
            lbody = liquefy(body, available_vars)
            if lval and lbody:
                return substitution_in_liquid(lbody, lval, name)
            return None
        case SHole(name):
            avars = available_vars or []
            return LiquidHornApplication(name=name,
                                         argtypes=[(LiquidVar(x), ty)
                                                   for (x, ty) in avars])
        case _:
            assert False


def basic_type(ty: Type) -> BaseType | TypeVar:
    match ty:
        case BaseType(_) | TypeVar(_):
            return ty
        case RefinedType(_, it, _):
            return basic_type(it)
        case Top():
            return BaseType("Unit")
        case _:
            assert False, f"Unknown base type {ty} ({type(ty)})"


def type_to_core(
    ty: SType,
    available_vars: list[tuple[str, BaseType | TypeVar]] | None = None
) -> Type:
    """Converts Surface Types into Core Types"""

    if available_vars is None:
        available_vars = []

    match normalize(ty):
        case SBaseType("Top"):
            return Top()
        case SBaseType(name):
            return BaseType(name)
        case STypeVar(name):
            return TypeVar(name)
        case SAbstractionType(name, vty, rty):
            nname = f"{name}__{len(available_vars)}"
            at = type_to_core(vty, available_vars)
            if isinstance(at, BaseType) or isinstance(
                    at, TypeVar) or isinstance(at, RefinedType):
                available_vars = available_vars + [(nname, basic_type(at))]
                nrty = substitution_sterm_in_stype(rty, SVar(nname), name)
            else:
                nrty = rty
            return AbstractionType(nname, at,
                                   type_to_core(nrty, available_vars))
        case STypePolymorphism(name, kind, rty):
            return TypePolymorphism(name, kind,
                                    type_to_core(rty, available_vars))
        case SRefinedType(name, ity, ref):
            basety = type_to_core(ity, available_vars)
            assert isinstance(basety, BaseType) or isinstance(
                basety, TypeVar) or isinstance(basety, TypeConstructor)
            return RefinedType(name, basety,
                               liquefy(ref, available_vars + [(name, basety)]))
        case STypeConstructor(name, args):
            return TypeConstructor(
                name, [type_to_core(ity, available_vars) for ity in args])
        case _:
            assert False, f"Unknown {ty} / {normalize(ty)}."


def lower_to_core(t: STerm) -> Term:
    """Converts Surface terms into Core terms."""
    match t:
        case SHole(name):
            return Hole(name)
        case SLiteral(val, ty):
            return Literal(val, type_to_core(ty))
        case SVar(name):
            return Var(name)
        case SIf(cond, then, otherwise):
            return If(lower_to_core(cond), lower_to_core(then),
                      lower_to_core(otherwise))
        case SApplication(fun, arg):
            return Application(lower_to_core(fun), lower_to_core(arg))
        case SLet(name, val, body):
            return Let(name, lower_to_core(val), lower_to_core(body))
        case SRec(name, ty, val, body):
            return Rec(name, type_to_core(ty), lower_to_core(val),
                       lower_to_core(body))
        case SAnnotation(expr, ty):
            return Annotation(lower_to_core(expr), type_to_core(ty))
        case SAbstraction(name, body):
            return Abstraction(name, lower_to_core(body))
        case STypeApplication(expr, ty):
            return TypeApplication(lower_to_core(expr), type_to_core(ty))
        case STypeAbstraction(name, kind, body):
            return TypeAbstraction(name, kind, lower_to_core(body))
        case _:
            assert False, f"{t} ({type(t)}) not supported"


def lower_to_core_context(elctx: ElaborationTypingContext) -> TypingContext:
    """Lowers the elaboration context down to the Core Typing Context."""
    tail: TypingContext = EmptyContext()

    for entry in elctx.entries[::-1]:
        match entry:
            case ElabVariableBinder(name, ty):
                tail = VariableBinder(tail, name, type_to_core(ty))
            case ElabUninterpretedBinder(name, ty):
                absty = type_to_core(ty)
                assert isinstance(absty, AbstractionType)
                tail = UninterpretedBinder(tail, name, absty)
            case ElabTypeVarBinder(name, kind):
                tail = TypeBinder(tail, name, kind)
            case ElabTypeDecl(name, args):
                tail = TypeConstructorBinder(tail, name, args)
            case _:
                assert False, f"{entry} not supported in Core."
    return tail
