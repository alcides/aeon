from __future__ import annotations
from dataclasses import dataclass
import typing
from loguru import logger
from aeon.utils.indented_logger import IndentedLogger
from aeon.core.liquid import LiquidApp, LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.types import (
    AbstractionType,
    LiquidHornApplication,
    RefinedType,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
    RefinimentPolymorphism,
    TypeVar,
    t_bool,
)
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_unit
from aeon.core.types import t_string
from aeon.prelude.prelude import native_types
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)

from aeon.utils.name import Name


class LiquidTypeCheckException(Exception):
    pass


@dataclass
class LiquidTypeCheckingContext:
    known_types: list[TypeConstructor]
    variables: dict[Name, TypeConstructor | TypeVar]
    functions: dict[Name, list[TypeConstructor | TypeVar]]


def lower_abstraction_type(ty: Type) -> list[TypeConstructor | TypeVar]:
    args: list[TypeConstructor | TypeVar] = []
    while True:
        match ty:
            # TODO: Should these be removed?
            case Top() | RefinedType(_, Top(), _):
                return args + [t_unit]
            case TypeVar(_):
                assert args
                return args + [ty]
            case (
                AbstractionType(_, RefinedType(_, aty, _), RefinedType(_, rty, _))
                | AbstractionType(_, RefinedType(_, aty, _), rty)
                | AbstractionType(_, aty, rty)
            ):
                match aty:
                    case TypeConstructor(_, _) | TypeVar(_):
                        args.append(aty)
                    case Top():
                        args.append(t_unit)
                    case _:
                        # For Higher-order functions, we use an int parameter.
                        args.append(t_int)
                ty = rty
            case TypePolymorphism(_, _, body):
                return lower_abstraction_type(body)
            case RefinimentPolymorphism(_, _, body):
                return lower_abstraction_type(body)
            case TypeConstructor(_, _):
                return args + [ty]
            case RefinedType(_, bt, _):
                return args + [bt]
            case _:
                assert False, f"Unknown type {ty} when lowering to liquid"


T = typing.TypeVar("T")


def flatten(xs: list[list[T]]) -> list[T]:
    return [x for y in xs for x in y]


def lower_context(ctx: TypingContext, indentedlogger: IndentedLogger = IndentedLogger()) -> LiquidTypeCheckingContext:
    known_types: list[Name] = native_types + []
    variables: dict[Name, TypeConstructor | TypeVar] = {}
    functions: dict[Name, list[TypeConstructor | TypeVar]] = {}

    indentedlogger.write("Lowering context for liquid type checking").indent("  ")
    for entry in ctx.entries[::-1]:
        # logger.log("AST_INFO", f"Lowering context entry: {entry}| {type(entry)}")
        match entry:
            case VariableBinder(name, TypeConstructor(_) as bt):
                variables[name] = bt
            case VariableBinder(name, TypeConstructor(_, _) as bt):
                variables[name] = bt
            case VariableBinder(name, TypeVar(tvname)):
                known_types.append(tvname)
                variables[name] = TypeVar(tvname)
            case VariableBinder(name, TypePolymorphism(_, _, _) as ty):
                functions[name] = lower_abstraction_type(ty)
            case VariableBinder(name, RefinimentPolymorphism(_, _, _) as ty):
                functions[name] = lower_abstraction_type(ty)
            case TypeBinder(name, _):
                known_types.append(name)
            case UninterpretedBinder(name, AbstractionType(_, _, _) as ty) | VariableBinder(
                name, AbstractionType(_, _, _) as ty
            ):
                functions[name] = lower_abstraction_type(ty)
            case UninterpretedBinder(name, TypePolymorphism(_, _, AbstractionType(_, _, _)) as ty):
                functions[name] = lower_abstraction_type(ty)
            case UninterpretedBinder(name, RefinimentPolymorphism(_, _, AbstractionType(_, _, _)) as ty):
                functions[name] = lower_abstraction_type(ty)
            case VariableBinder(name, RefinedType(_, TypeConstructor(_) as bt, _)):
                variables[name] = bt
            case VariableBinder(name, RefinedType(_, TypeConstructor(_, _) as bt, _)):
                variables[name] = bt
            case VariableBinder(name, RefinedType(_, TypeVar(tvname) as ty, _)):
                known_types.append(tvname)

            case TypeConstructorBinder(_, _):
                pass
            case _:
                indentedlogger.write(f"Unknown context type {entry} ({type(entry)})")
                logger.log("AST_INFO", f"Unknown context type {entry} ({type(entry)})")
                assert False, f"Unknown context type {entry} ({type(entry)})"

    indentedlogger.dedent().write("Lowered context for liquid type checking:").indent("  ")
    indentedlogger.write("Known types:").indent("  ")
    for name in known_types:
        indentedlogger.write(f"{name}")
    indentedlogger.dedent().write("Variables:").indent("  ")
    for name, var in variables.items():
        indentedlogger.write(f"{name}: {var}")
    indentedlogger.dedent().write("Functions:").indent("  ")
    for name, funs in functions.items():
        indentedlogger.write(f"{name}: {funs}")
    indentedlogger.dedent()

    logger.log("AST_INFO", f"Known types: {known_types}")
    logger.log("AST_INFO", f"Variables: {variables}")
    logger.log("AST_INFO", f"Functions: {functions}")

    return LiquidTypeCheckingContext([TypeConstructor(n) for n in known_types], variables, functions)


def type_infer_liquid(
    ctx: LiquidTypeCheckingContext,
    liq: LiquidTerm,
    indentedlogger: IndentedLogger = IndentedLogger(),
) -> TypeConstructor | TypeVar:
    # logger.log("AST_INFO", f"Type inferring liquid term {liq}")
    match liq:
        case LiquidLiteralBool(_):
            return t_bool
        case LiquidLiteralInt(_):
            return t_int
        case LiquidLiteralFloat(_):
            return t_float
        case LiquidLiteralString(_):
            return t_string
        case LiquidVar(name):
            indentedlogger.write(f"Type inferring liquid variable {name}")
            logger.log("AST_INFO", f"Looking up variable {name} in context {ctx.variables}")
            if name not in ctx.variables:
                raise LiquidTypeCheckException(f"Variable {name} not in context in {ctx}.")

            match ctx.variables[name]:
                case TypeConstructor(_, []) as ty:
                    return ty
                case TypeConstructor(_, _):
                    return t_int
                case TypeVar(_) as ty:
                    return ty
                case _:
                    raise LiquidTypeCheckException("Could not find type for {liq} ({ctx.variables[name]})")
        case LiquidApp(fun, args):
            indentedlogger.write(f"Type inferring liquid application {liq} with function {fun} and args {args}")
            logger.log("AST_INFO", f"Type inferring liquid application {liq} with function {fun} and args {args}")
            # logger.log("AST_INFO", f"Context: \n{ "\n".join([f"{fname}: {body}" for fname, body in ctx.functions.items()])}")
            if fun not in ctx.functions:
                raise LiquidTypeCheckException(f"Function {fun} not in context in {liq} ({ctx.functions}).")
            ftype = ctx.functions[fun]
            logger.log("AST_INFO", f"Function type: {ftype}")
            equalities: dict[Name, TypeConstructor | TypeVar] = {}

            def resolve_type(ty: Type) -> TypeConstructor | TypeVar:
                match ty:
                    case TypeConstructor(_, _):
                        logger.log("AST_INFO", f"Resolving type {ty} as TypeConstructor")
                        return ty
                    case TypeVar(tv):
                        if tv in equalities:
                            eq = equalities[tv]
                            if tv == eq.name:
                                logger.log("AST_INFO", f"Resolving type {ty} as TypeVar with equality {eq}")
                                return eq
                            logger.log("AST_INFO", f"Resolving type {ty} as TypeVar with equality {equalities[tv]}")
                            return resolve_type(equalities[tv])
                        else:
                            logger.log("AST_INFO", f"Resolving type {ty} as TypeVar")
                            return ty
                    case _:
                        logger.log("AST_ERROR", f"Unknown type {ty} in resolve_type")
                        assert False, "unknown stuff"

            if len(ftype) != len(args) + 1:
                raise LiquidTypeCheckException(
                    f"Function application {liq} needs {len(ftype) - 1} arguments, but was passed {len(args)}."
                )
            type_of_args = []

            for arg, exp_t in zip(args, ftype):
                k = type_infer_liquid(ctx, arg)
                type_of_args.append(k)
                match (k, exp_t):
                    case (TypeConstructor(t), TypeConstructor(e)):
                        if t != e:
                            raise LiquidTypeCheckException(
                                f"Argument {arg} in {liq} is expected to be of type {exp_t}, but {k} was found instead."
                            )
                    case (TypeConstructor(t), TypeVar(name)):
                        if name not in equalities:
                            equalities[name] = resolve_type(k)
                        elif resolve_type(TypeVar(name)) != k:
                            raise LiquidTypeCheckException(
                                f"Argument {arg} in {liq} is expected to be of type {exp_t} ({equalities[name]}), but {k} was found instead."
                            )
                    case (TypeVar(t), TypeVar(name)):
                        if name not in equalities:
                            equalities[name] = resolve_type(k)
                        elif resolve_type(TypeVar(name)) != k:
                            raise LiquidTypeCheckException(
                                f"Argument {arg} in {liq} is expected to be of type {exp_t}, but {k} was found instead."
                            )
                    case _:
                        raise LiquidTypeCheckException(
                            f"Could not unify {k} ({type(k)}) and {exp_t} ({type(exp_t)}) in {liq}."
                        )

            def is_base_type_in(t: Type, names: list[str]) -> bool:
                match t:
                    case TypeConstructor(Name(name, _)):
                        return name in names
                    case _:
                        return False

            first_argument = type_of_args[0]
            match fun:
                case Name(fun_name, _):
                    if fun_name in ["<", "<=", ">", ">="]:
                        if not is_base_type_in(first_argument, ["Float", "Int"]) and not isinstance(
                            type_of_args[0], TypeVar
                        ):
                            raise LiquidTypeCheckException(f"Function {fun_name} only applies to Floats or Ints.")
                    elif fun_name in ["==", "!="] and not isinstance(first_argument, TypeVar):
                        # TODO: Add type equality
                        if not is_base_type_in(first_argument, ["Unit", "Bool", "Float", "Int", "String"]):
                            raise LiquidTypeCheckException(f"Function {fun_name} only applies to built-in types.")
                    elif fun_name in ["+", "-", "*", "/"] and not isinstance(first_argument, TypeVar):
                        if not is_base_type_in(first_argument, ["Float", "Int"]):
                            raise LiquidTypeCheckException(f"Function {fun_name} only applies to Floats or Ints.")
            indentedlogger.write(f"Function {fun} applied to {args} has type {ftype[-1]}.")
            logger.log("AST_INFO", f"Function {fun} applied to {args} has type {ftype[-1]}.")
            logger.log(
                "AST_INFO", f"Equalities: \n{'\n'.join([f'{ename}: {body}' for ename, body in equalities.items()])}"
            )
            return resolve_type(ftype[-1])
        case LiquidHornApplication(_, _):
            return t_bool
        case _:
            logger.log("AST_INFO", f"Constructed {liq} ({type(liq)}) not supported.")
            assert False, f"Constructed {liq} ({type(liq)}) not supported."


def check_liquid(
    ctx: LiquidTypeCheckingContext,
    liq: LiquidTerm,
    exp: TypeConstructor,
) -> bool:
    try:
        t = type_infer_liquid(ctx, liq)
        return t == exp
    except LiquidTypeCheckException:
        logger.log("AST_ERROR", f"Liquid type check failed for {liq} with expected type {exp}.")
        return False


def typecheck_liquid(
    ctx: TypingContext,
    liq: LiquidTerm,
    indentedlogger: IndentedLogger = IndentedLogger(),
) -> Type | None:
    assert isinstance(ctx, TypingContext)
    # logger.log("AST_INFO", f"Lowering context for liquid type checking")
    indentedlogger.write("Lowering context for liquid type checking").indent("  ")
    lctx = lower_context(ctx, indentedlogger=indentedlogger)
    indentedlogger.dedent().write(f"Lowered context for liquid type checking: {lctx}")
    # logger.log("AST_INFO", f"Typechecking liquid term {liq}")
    v = type_infer_liquid(lctx, liq, indentedlogger=indentedlogger.indent("  "))
    indentedlogger.dedent().write(f"Typechecked liquid term {liq} as {v}")
    logger.log("AST_INFO", f"Typechecked liquid term {liq} as {v}")
    return v
