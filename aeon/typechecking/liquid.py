from __future__ import annotations
from dataclasses import dataclass
import typing

from aeon.core.liquid import LiquidApp, LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.types import (
    AbstractionType,
    BaseType,
    LiquidHornApplication,
    RefinedType,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
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
    known_types: list[BaseType]
    variables: dict[Name, BaseType | TypeVar | TypeConstructor]
    functions: dict[Name, list[BaseType | TypeVar | TypeConstructor]]


def lower_abstraction_type(ty: Type) -> list[BaseType | TypeVar | TypeConstructor]:
    args: list[BaseType | TypeVar | TypeConstructor] = []
    while True:
        match ty:
            # TODO: Should these be removed?
            case Top() | RefinedType(_, Top(), _):
                return args + [t_unit]
            case BaseType(_) | TypeVar(_):
                assert args
                return args + [ty]
            case (
                AbstractionType(_, RefinedType(_, aty, _), RefinedType(_, rty, _))
                | AbstractionType(_, RefinedType(_, aty, _), rty)
                | AbstractionType(_, aty, rty)
            ):
                match aty:
                    case BaseType(_) | TypeVar(_):
                        args.append(aty)
                    case Top():
                        args.append(t_unit)
                    case _:
                        # For Higher-order functions, we use an int parameter.
                        args.append(t_int)
                ty = rty
            case TypePolymorphism(_, _, body):
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


def lower_context(ctx: TypingContext) -> LiquidTypeCheckingContext:
    known_types: list[Name] = native_types + []
    variables: dict[Name, BaseType | TypeVar | TypeConstructor] = {}
    functions = {}

    for entry in ctx.entries[::-1]:
        match entry:
            case VariableBinder(name, BaseType(_) as bt):
                variables[name] = bt
            case VariableBinder(name, TypeVar(tvname)):
                known_types.append(tvname)
                variables[name] = TypeVar(tvname)
            case VariableBinder(name, TypePolymorphism(_) as ty):
                functions[name] = lower_abstraction_type(ty)
            case TypeBinder(name, _):
                known_types.append(name)
            case UninterpretedBinder(name, AbstractionType(_, _, _) as ty) | VariableBinder(
                name, AbstractionType(_, _, _) as ty
            ):
                functions[name] = lower_abstraction_type(ty)
            case VariableBinder(name, RefinedType(_, BaseType(_) as bt, _)):
                variables[name] = bt
            case TypeConstructorBinder(_, _):
                pass
            case _:
                assert False, f"Unknown context type ({type(ctx)})"

    return LiquidTypeCheckingContext([BaseType(n) for n in known_types], variables, functions)


def type_infer_liquid(
    ctx: LiquidTypeCheckingContext,
    liq: LiquidTerm,
) -> BaseType | TypeConstructor | TypeVar:
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
            if name not in ctx.variables:
                raise LiquidTypeCheckException(f"Variable {name} not in context in {ctx}.")

            rt = ctx.variables[name]
            assert isinstance(rt, BaseType) or isinstance(rt, TypeVar)
            return rt
        case LiquidApp(fun, args):
            if fun not in ctx.functions:
                raise LiquidTypeCheckException(f"Function {fun} not in context in {liq} ({ctx.functions}).")
            ftype = ctx.functions[fun]
            equalities: dict[Name, BaseType | TypeVar] = {}

            def resolve_type(ty: Type) -> BaseType | TypeVar:
                match ty:
                    case BaseType(_):
                        return ty
                    case TypeVar(tv):
                        if tv in equalities:
                            return resolve_type(equalities[tv])
                        else:
                            return ty
                    case _:
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
                    case (BaseType(t), BaseType(e)):
                        if t != e:
                            raise LiquidTypeCheckException(
                                f"Argument {arg} in {liq} is expected to be of type {exp_t}, but {k} was found instead."
                            )
                    case (BaseType(t), TypeVar(name)):
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
                        assert False, (
                            f"Case not considered in liquid unification: {k} ({type(k)}) and {exp_t} ({type(exp_t)})"
                        )

            def is_base_type_in(t: Type, names: list[str]) -> bool:
                match t:
                    case BaseType(Name(name, _)):
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
            return resolve_type(ftype[-1])
        case LiquidHornApplication(_, _):
            return t_bool
        case _:
            assert False, f"Constructed {liq} ({type(liq)}) not supported."


def check_liquid(
    ctx: LiquidTypeCheckingContext,
    liq: LiquidTerm,
    exp: BaseType,
) -> bool:
    try:
        t = type_infer_liquid(ctx, liq)
        return t == exp
    except LiquidTypeCheckException:
        return False


def typecheck_liquid(
    ctx: TypingContext,
    liq: LiquidTerm,
) -> Type | None:
    assert isinstance(ctx, TypingContext)
    v = type_infer_liquid(lower_context(ctx), liq)
    return v
