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
    ExistentialType,
    LiquidHornApplication,
    RefinedType,
    RefinementPolymorphism,
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
    known_types: list[TypeConstructor]
    variables: dict[Name, TypeConstructor | TypeVar]
    functions: dict[Name, list[TypeConstructor | TypeVar]]

    def __repr__(self):
        kt = "; ".join([str(t) for t in self.known_types])
        vars = "; ".join([str(t) + ":" + str(self.variables[t]) for t in self.variables])
        fns = "; ".join([str(t) for t in self.functions])
        return f"(LiquidGamma {kt} | {vars} | {fns} )"


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
            case RefinementPolymorphism(_, _, body):
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
    variables: dict[Name, TypeConstructor | TypeVar] = {}
    functions = {}

    def add_variable(name: Name, ty: Type) -> None:
        """Record a variable binding for liquid lookup. ``ExistentialType``
        wrappers are peeled — each ``(bn, bt)`` binder inside is registered
        recursively as if it were its own ``VariableBinder``, then the bare
        body is handled. This mirrors what ``wellformed`` does and lets
        refinements over Form B existentials reach the SMT context."""
        match ty:
            case ExistentialType(binders, body):
                for bn, bt in binders:
                    add_variable(bn, bt)
                add_variable(name, body)
            case TypeConstructor(_) | TypeConstructor(_, _):
                variables[name] = ty
            case TypeVar(tvname):
                known_types.append(tvname)
                variables[name] = ty
            case RefinedType(_, TypeConstructor(_) as bt, _) | RefinedType(_, TypeConstructor(_, _) as bt, _):
                variables[name] = bt
            case RefinedType(_, TypeVar(tvname) as bt, _):
                known_types.append(tvname)
                variables[name] = bt
            case TypePolymorphism(_, _, _) | RefinementPolymorphism(_, _, _) | AbstractionType(_, _, _):
                functions[name] = lower_abstraction_type(ty)
            case _:
                assert False, f"Unsupported variable binder type {ty} ({type(ty)})"

    for entry in ctx.entries[::-1]:
        match entry:
            case VariableBinder(name, ty):
                add_variable(name, ty)
            case TypeBinder(name, _):
                known_types.append(name)
            case UninterpretedBinder(
                name,
                AbstractionType(_, _, _) | TypePolymorphism(_, _, _) | RefinementPolymorphism(_, _, _) as ty,
            ):
                # ``lower_abstraction_type`` already recurses through
                # ``TypePolymorphism`` / ``RefinementPolymorphism`` to the
                # underlying ``AbstractionType``.
                functions[name] = lower_abstraction_type(ty)
            case TypeConstructorBinder(_, _):
                pass
            case _:
                assert False, f"Unknown context type {entry} ({type(entry)})"

    return LiquidTypeCheckingContext([TypeConstructor(n) for n in known_types], variables, functions)


def type_infer_liquid(
    ctx: LiquidTypeCheckingContext,
    liq: LiquidTerm,
) -> TypeConstructor | TypeVar:
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

            match ctx.variables[name]:
                case TypeConstructor(_, []) as ty:
                    return ty
                case TypeConstructor(_, _) as ty:
                    return ty
                case TypeVar(_) as ty:
                    return ty
                case _:
                    raise LiquidTypeCheckException("Could not find type for {liq} ({ctx.variables[name]})")
        case LiquidApp(fun, args):
            if fun not in ctx.functions:
                raise LiquidTypeCheckException(f"Function {fun} not in context in {liq} ({ctx.functions}).")
            ftype = ctx.functions[fun]
            equalities: dict[Name, TypeConstructor | TypeVar] = {}

            def resolve_type(ty: Type) -> TypeConstructor | TypeVar:
                match ty:
                    case TypeConstructor(_, _):
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

            def _unify(actual: Type, expected: Type) -> None:
                """Walk ``actual`` against ``expected``, populating ``equalities``.

                Polymorphic uninterpreted functions (e.g. auto-generated
                inductive projections like ``Pair_mk_fst : forall a b,
                (Pair a b) -> a``) reach the liquid layer with TypeVars
                in argument positions. Without descending into the args
                of a TypeConstructor, the return type ``a`` would never
                be bound to the concrete type at the call site.
                """
                match (actual, expected):
                    case (_, TypeVar(name)):
                        resolved = resolve_type(actual) if isinstance(actual, (TypeConstructor, TypeVar)) else actual
                        if name in equalities:
                            if resolve_type(TypeVar(name)) != resolved:
                                raise LiquidTypeCheckException(
                                    f"Argument {arg} in {liq} is expected to be of type "
                                    f"{exp_t} ({equalities[name]}), but {k} was found instead."
                                )
                        else:
                            assert isinstance(resolved, (TypeConstructor, TypeVar))
                            equalities[name] = resolved
                    case (TypeConstructor(t, a_args), TypeConstructor(e, e_args)) if t == e and len(a_args) == len(
                        e_args
                    ):
                        for a_in, e_in in zip(a_args, e_args):
                            _unify(a_in, e_in)
                    case (TypeConstructor(t), TypeConstructor(e)):
                        raise LiquidTypeCheckException(
                            f"Argument {arg} in {liq} is expected to be of type {exp_t}, but {k} was found instead."
                        )
                    case _:
                        raise LiquidTypeCheckException(
                            f"Could not unify {actual} ({type(actual)}) and {expected} ({type(expected)}) in {liq}."
                        )

            for arg, exp_t in zip(args, ftype):
                k = type_infer_liquid(ctx, arg)
                type_of_args.append(k)
                _unify(k, exp_t)

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
                        if not (
                            is_base_type_in(first_argument, ["Unit", "Bool", "Float", "Int", "String", "Set"])
                            or isinstance(first_argument, TypeConstructor)
                        ):
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
    exp: TypeConstructor,
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
