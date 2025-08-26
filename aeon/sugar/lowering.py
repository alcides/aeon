from loguru import logger

from aeon.utils.indented_logger import IndentedLogger

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.types import LiquidHornApplication, TypeConstructor, t_int
from aeon.core.substitutions import substitution_in_liquid, substitute_vartype
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
    RefinementApplication,
    Var,
    Hole,
)
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Type,
    TypePolymorphism,
    RefinimentPolymorphism,
    Top,
    TypeVar,
    t_unit,
)
from aeon.elaboration.context import (
    ElabTypeDecl,
    ElabTypeVarBinder,
    ElabTypingContextEntry,
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
    SRefinementApplication,
    SVar,
    SHole,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SType,
    STypeConstructor,
    STypePolymorphism,
    SRefinementPolymorphism,
    STypeVar,
)
from aeon.sugar.substitutions import normalize, substitution_sterm_in_sterm, substitution_sterm_in_stype
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    TypingContextEntry,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.utils.name import Name, fresh_counter


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
        logger.log("AST_INFO", f"Cannot liquefy application {app}.")
        return None

    match fun:
        case SVar(name):
            return LiquidApp(name, [arg], loc=app.loc)
        case SApplication(_, _):
            liquid_pseudo_fun = liquefy_app(fun)
            if liquid_pseudo_fun:
                return LiquidApp(liquid_pseudo_fun.fun, liquid_pseudo_fun.args + [arg], loc=app.loc)
            return None
        case SLet(name, val, body):
            app = SApplication(substitution_sterm_in_sterm(body, val, name), app.arg, loc=app.loc)
            return liquefy_app(app)
        case _:
            raise LiquefactionException(f"{app} is not a valid predicate.")


def liquefy(t: STerm, available_vars: list[tuple[Name, TypeConstructor | TypeVar]] | None = None) -> LiquidTerm:
    """Converts Surface Terms into Liquid Terms"""
    match t:
        case SLiteral(val, STypeConstructor(Name("Bool", _)), loc):
            assert isinstance(val, bool)
            return LiquidLiteralBool(val, loc=loc)
        case SLiteral(val, STypeConstructor(Name("Int", _)), loc):
            assert isinstance(val, int)
            return LiquidLiteralInt(val, loc=loc)
        case SLiteral(val, STypeConstructor(Name("Float", _)), loc):
            assert isinstance(val, float)
            return LiquidLiteralFloat(val, loc=loc)
        case SLiteral(val, STypeConstructor(Name("String", _)), loc):
            assert isinstance(val, str)
            return LiquidLiteralString(val, loc=loc)
        case SLiteral(_, _):
            assert False, f"{t} is not convertable to liquid term."
        case SVar(name, loc):
            return LiquidVar(name, loc=loc)
        case SIf(cond, then, otherwise, loc):
            co = liquefy(cond, available_vars)
            th = liquefy(then, available_vars)
            ot = liquefy(otherwise, available_vars)
            if co is not None and th is not None and ot is not None:
                return LiquidApp(Name("ite", 0), [co, th, ot], loc=loc)
            logger.log("AST_INFO", f"Cannot liquefy if {t}.")
            return None
        case SAnnotation(expr, _):
            return liquefy(expr, available_vars)
        case SAbstraction(name, body):
            logger.log("AST_INFO", f"Cannot liquefy abstraction {t}.")
            return None
        case STypeApplication(expr, _):
            return liquefy(expr, available_vars)
        case SRefinementApplication(expr, _):
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
            logger.log("AST_INFO", f"Cannot liquefy let {t}.")
            return None
        case SRec(name, _, val, body):
            lval = liquefy(val, available_vars)  # TODO: induction?
            lbody = liquefy(body, available_vars)
            if lval and lbody:
                return substitution_in_liquid(lbody, lval, name)
            logger.log("AST_INFO", f"Cannot liquefy rec {t}.")
            return None
        case SHole(name):
            avars = available_vars or []
            return LiquidHornApplication(name=name, argtypes=[(LiquidVar(x), ty) for (x, ty) in avars])
        case _:
            assert False


def basic_type(ty: Type) -> TypeConstructor | TypeVar:
    match ty:
        case TypeConstructor(_, _) | TypeVar(_):
            return ty
        case RefinedType(_, it, _):
            return basic_type(it)
        case Top():
            return t_unit
        case _:
            assert False, f"Unknown base type {ty} ({type(ty)})"


def type_to_core(
    ty: SType,
    indlog: IndentedLogger = IndentedLogger(),
    available_vars: list[tuple[Name, TypeConstructor | TypeVar]] | None = None,
) -> Type:
    """Converts Surface Types into Core Types"""

    if available_vars is None:
        available_vars = []

    match normalize(ty):
        case STypeConstructor(Name("Top", 0), loc):
            indlog.write("Lowering Top type")
            return Top()  # TODO: loc?
        case STypeVar(name, loc):
            indlog.write(f"Lowering type var {name}")
            return TypeVar(name, loc=loc)
        case SAbstractionType(name, vty, rty, loc):
            indlog.write(f"Lowering abstraction type {name}: {vty} -> {rty}").write(f"├─ Var type: {vty}").indent("│  ")
            nname = Name(name.name, fresh_counter.fresh())
            at = type_to_core(vty, indlog, available_vars)
            if isinstance(at, TypeConstructor) or isinstance(at, TypeVar) or isinstance(at, RefinedType):
                available_vars = available_vars + [(nname, basic_type(at))]
                nrty = substitution_sterm_in_stype(rty, SVar(nname), name)
            else:
                nrty = rty
            indlog.dedent().write(f"└─ Return type {rty}").indent("   ")
            lnrty = type_to_core(nrty, indlog, available_vars)
            indlog.dedent()
            return AbstractionType(nname, at, lnrty, loc=loc)
        case STypePolymorphism(name, kind, rty, loc):
            indlog.write(f"Lowering type polymorphism ∀{name}:{kind}. {rty}").write(f"└─ Return type {rty}").indent(
                "   "
            )
            lrty = type_to_core(rty, indlog, available_vars)
            indlog.dedent()
            return TypePolymorphism(name, kind, lrty, loc=loc)
        case SRefinementPolymorphism(name, type, ref, loc):
            indlog.write(f"Lowering refinement polymorphism ∀{name}:{type}. {ref}").write(
                f"├─ Base type {type}"
            ).indent("│  ")
            ltype = type_to_core(type, indlog, available_vars)
            indlog.dedent().write(f"└─ Refinement {ref}").indent("   ")
            lref = type_to_core(ref, indlog, available_vars)
            indlog.dedent()
            return RefinimentPolymorphism(name, ltype, lref, loc=loc)
        case SRefinedType(oname, ity, ref, loc):
            indlog.write(f"Lowering refined type {{{oname}: {ity} | {ref}}}").write(f"└─ Base type {ity}").indent("   ")
            if oname.id == -1:
                name = Name(oname.name, fresh_counter.fresh())
                ref = substitution_sterm_in_sterm(ref, SVar(name), oname)
            else:
                name = oname
            basety = type_to_core(ity, indlog, available_vars)
            indlog.dedent()
            assert (
                isinstance(basety, TypeConstructor)
                or isinstance(basety, TypeVar)
                or isinstance(basety, TypeConstructor)
            )
            return RefinedType(name, basety, liquefy(ref, available_vars + [(name, basety)]), loc=loc)
        case STypeConstructor(name, args, loc):
            indlog.write(f"Lowering type constructor {name}")

            def internal(ity: SType, isLast: bool) -> Type:
                indlog.write(f"{'└─ Argument' if isLast else '├─ Argument'} {ity}").indent("  " if isLast else "│ ")
                ity_core = type_to_core(ity, indlog, available_vars)
                indlog.dedent()
                return ity_core

            return TypeConstructor(name, [internal(ity, i + 1 == len(args)) for i, ity in enumerate(args)], loc=loc)
        case _:
            assert False, f"Unknown {ty} / {normalize(ty)}."


def lower_to_core(t: STerm, indlog: IndentedLogger) -> Term:
    """Converts Surface terms into Core terms."""
    match t:
        case SHole(name, loc):
            indlog.write(f"Lowering hole {name}")
            return Hole(name, loc=loc)
        case SLiteral(val, ty, loc):
            indlog.write(f"Lowering literal {val}").indent("")
            v = Literal(val, type_to_core(ty, indlog), loc=loc)
            indlog.dedent()
            return v
        case SVar(name, loc):
            indlog.write(f"Lowering var {name}")  # └ ├ ─ │
            return Var(name, loc=loc)
        case SIf(cond, then, otherwise, loc):
            indlog.write("Lowering if").write("├─ Condition").indent("│  ")
            lcond = lower_to_core(cond, indlog)
            indlog.dedent().write("├─ Then").indent("│  ")
            lthen = lower_to_core(then, indlog)
            indlog.dedent().write("└─ Otherwise").indent("   ")
            lotherwise = lower_to_core(otherwise, indlog)
            indlog.dedent()
            return If(lcond, lthen, lotherwise, loc=loc)
        case SApplication(fun, arg, loc):
            indlog.write("Lowering application").write("├─ Function").indent("│  ")
            lfun = lower_to_core(fun, indlog)
            indlog.dedent().write("└─ Argument").indent("   ")
            larg = lower_to_core(arg, indlog)
            indlog.dedent()
            return Application((lfun), (larg), loc=loc)
        case SLet(name, val, body, loc):
            indlog.write(f"Lowering let {name}").write("├─ Value").indent("│  ")
            lval = lower_to_core(val, indlog)
            indlog.dedent().write("└─ Body").indent("   ")
            lbody = lower_to_core(body, indlog)
            indlog.dedent()
            return Let(name, (lval), (lbody), loc=loc)
        case SRec(name, ty, val, body, loc):
            indlog.write(f"Lowering rec {name}").write("├─ Type").indent("│  ")
            lty = type_to_core(ty, indlog)
            indlog.dedent().write(f"├─ Value {val}").indent("│  ")
            lval = lower_to_core(val, indlog)
            indlog.dedent().write("└─ Body").indent("   ")
            lbody = lower_to_core(body, indlog)
            indlog.dedent()
            return Rec(name, (lty), (lval), (lbody), loc=loc)
        case SAnnotation(expr, ty, loc):
            indlog.write("Lowering annotation").write("├─ Expression").indent("│  ")
            lexpr = lower_to_core(expr, indlog)
            indlog.dedent().write("└─ Type").indent("   ")
            lty = type_to_core(ty, indlog)
            indlog.dedent()
            return Annotation((lexpr), (lty), loc=loc)
        case SAbstraction(name, body, loc):
            indlog.write(f"Lowering abstraction {name} -> {body}").write(f"└─ Body {body}").indent("   ")
            lbody = lower_to_core(body, indlog)
            indlog.dedent()
            return Abstraction(name, (lbody), loc=loc)
        case STypeApplication(expr, ty, loc):
            indlog.write("Lowering type application").write("├─ Expression").indent("│  ")
            lexpr = lower_to_core(expr, indlog)
            indlog.dedent().write("└─ Type").indent("   ")
            lty = type_to_core(ty, indlog)
            indlog.dedent()
            return TypeApplication((lexpr), (lty), loc=loc)
        case SRefinementApplication(expr, ty, loc):
            indlog.write("Lowering refinement application").write("├─ Expression").indent("│  ")
            lexpr = lower_to_core(expr, indlog)
            indlog.dedent().write("└─ Type").indent("   ")
            lty = type_to_core(ty, indlog)
            indlog.dedent()
            return RefinementApplication((lexpr), (lty), loc=loc)
        case STypeAbstraction(name, kind, body, loc):
            indlog.write(f"Lowering type abstraction ∀{name}:{kind} -> {body}").write(f"└─ Body {body}").indent("   ")
            lbody = lower_to_core(body, indlog)
            indlog.dedent()
            return TypeAbstraction(name, kind, (lbody), loc=loc)
        case _:
            assert False, f"{t} ({type(t)}) not supported"


def monomorphic_type(ty: Type) -> AbstractionType:
    match ty:
        case TypePolymorphism(name, _, body):
            return monomorphic_type(substitute_vartype(body, t_int, name))
        case RefinimentPolymorphism(name, _, body):
            return monomorphic_type(substitute_vartype(body, t_unit, name))
        case AbstractionType(_, _, _):
            return ty
        case _:
            assert False, f"Type {ty} is not a monomorphic type, cannot be used in uninterpreted binders."


def wrap_ctx_entry(e: ElabTypingContextEntry) -> TypingContextEntry:
    match e:
        case ElabVariableBinder(name, ty):
            return VariableBinder(name, type_to_core(ty))
        case ElabUninterpretedBinder(name, ty):
            absty = type_to_core(ty)
            concrete_absty = monomorphic_type(absty)
            return UninterpretedBinder(name, concrete_absty)
        case ElabTypeVarBinder(name, kind):
            return TypeBinder(name, kind)
        case ElabTypeDecl(name, args):
            return TypeConstructorBinder(name, args)
        case _:
            assert False, f"{e} not supported in Core."


def lower_to_core_context(elctx: ElaborationTypingContext) -> TypingContext:
    """Lowers the elaboration context down to the Core Typing Context."""
    return TypingContext([wrap_ctx_entry(e) for e in elctx.entries])
