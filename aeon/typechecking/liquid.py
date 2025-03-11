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
from aeon.core.types import t_string
from aeon.prelude.prelude import native_types
from aeon.typechecking.context import (
    EmptyContext,
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
)


class LiquidTypeCheckException(Exception):
    pass


@dataclass
class LiquidTypeCheckingContext:
    known_types: list[BaseType]
    variables: dict[str, BaseType | TypeVar | TypeConstructor]
    functions: dict[str, list[BaseType | TypeVar | TypeConstructor]]


def lower_abstraction_type(
        ty: Type) -> list[BaseType | TypeVar | TypeConstructor]:
    args: list[BaseType | TypeVar | TypeConstructor] = []
    while True:
        match ty:
        # TODO: Should these be removed?
            case Top() | RefinedType(_, Top(), _):
                return args + [BaseType("Unit")]
            case BaseType(_) | TypeVar(_):
                assert args
                return args + [ty]
            case (AbstractionType(_, RefinedType(_, aty, _),
                                  RefinedType(_, rty, _))
                  | AbstractionType(_, RefinedType(_, aty, _), rty)
                  | AbstractionType(_, aty, rty)):
                match aty:
                    case BaseType(_) | TypeVar(_):
                        args.append(aty)
                    case Top():
                        args.append(BaseType("Unit"))
                    case _:
                        # For Higher-order functions, we use an int parameter.
                        args.append(BaseType("Int"))
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
    known_types: list[str] = native_types + []
    variables: dict[str, BaseType | TypeVar | TypeConstructor] = {}
    functions = {}
    while not isinstance(ctx, EmptyContext):
        match ctx:
            case VariableBinder(prev, name, BaseType(_) as bt):
                variables[name] = bt
                ctx = prev
            case VariableBinder(prev, name, TypeVar(tvname)):
                known_types.append(tvname)
                variables[name] = BaseType(tvname)
                ctx = prev
            case VariableBinder(prev, name, TypePolymorphism(_) as ty):
                functions[name] = lower_abstraction_type(ty)
                ctx = prev
            case TypeBinder(prev, name, _):
                known_types.append(name)
                ctx = prev
            case UninterpretedBinder(prev, name,
                                     AbstractionType(_, _, _) as
                                     ty) | VariableBinder(
                                         prev, name,
                                         AbstractionType(_, _, _) as ty):
                functions[name] = lower_abstraction_type(ty)
                ctx = prev
            case VariableBinder(prev, name,
                                RefinedType(_,
                                            BaseType(_) as bt, _)):
                variables[name] = bt
                ctx = prev
            case TypeConstructorBinder(prev, _, _):
                ctx = prev
            case _:
                assert False, f"Unknown context type ({type(ctx)})"

    return LiquidTypeCheckingContext([BaseType(n) for n in known_types],
                                     variables, functions)


def type_infer_liquid(
    ctx: LiquidTypeCheckingContext,
    liq: LiquidTerm,
) -> BaseType | TypeConstructor:
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
                raise LiquidTypeCheckException(
                    f"Variable {name} not in context in {liq}.")
            rt = ctx.variables[name]
            assert isinstance(rt, BaseType)
            return rt
        case LiquidApp(fun, args):
            if fun not in ctx.functions:
                raise LiquidTypeCheckException(
                    f"Function {fun} not in context in {liq} ({ctx.functions})."
                )
            ftype = ctx.functions[fun]
            equalities: dict[str, BaseType] = {}

            if len(ftype) != len(args) + 1:
                raise LiquidTypeCheckException(
                    f"Function application {liq} needs {len(ftype)-1} arguments, but was passed {len(args)}."
                )

            for arg, exp_t in zip(args, ftype):
                k = type_infer_liquid(ctx, arg)
                match (k, exp_t):
                    case (BaseType(t), BaseType(e)):
                        if t != e:
                            raise LiquidTypeCheckException(
                                f"Argument {arg} in {liq} is expected to be of type {exp_t}, but {k} was found instead."
                            )
                    case (BaseType(t), TypeVar(name)):
                        if name not in equalities:
                            equalities[name] = k
                        elif equalities[name] != k:
                            raise LiquidTypeCheckException(
                                f"Argument {arg} in {liq} is expected to be of type {exp_t} ({equalities[name]}), but {k} was found instead."
                            )
                    case _:
                        assert False, "Case not considered in liquid unification"

            if isinstance(ftype[-1], TypeVar):
                return equalities[ftype[-1].name]
            return ftype[-1]
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
    return type_infer_liquid(lower_context(ctx), liq)
