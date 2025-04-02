from __future__ import annotations

from dataclasses import dataclass
from functools import reduce
from typing import Any
from typing import Generator
from loguru import logger

from z3 import Function
from z3 import Int
from z3 import Solver
from z3 import sat
from z3 import unknown
from z3.z3 import And
from z3.z3 import Bool
from z3.z3 import BoolRef
from z3.z3 import BoolSort
from z3.z3 import Const
from z3.z3 import DeclareSort
from z3.z3 import FP
from z3.z3 import FPSort
from z3.z3 import Float64
from z3.z3 import Implies
from z3.z3 import IntSort
from z3.z3 import Not
from z3.z3 import Or
from z3.z3 import String
from z3.z3 import StringSort
from z3.z3 import SortRef
from z3.z3types import Z3Exception

from aeon.core.liquid import LiquidApp
from aeon.core.types import LiquidHornApplication, TypeConstructor
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, RefinedType, Top, TypePolymorphism
from aeon.core.types import BaseType
from aeon.core.types import Type
from aeon.core.types import TypeVar
from aeon.core.types import t_bool, t_int, t_float, t_string, t_unit
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.vcs import UninterpretedFunctionDeclaration
from aeon.utils.name import Name, fresh_counter

smt_function_types: dict[str, list[Type]] = {
    "smtEqInt": [t_int, t_int, t_bool],
    "smtEqFloat": [t_float, t_float, t_bool],
    "smtEqBool": [t_float, t_float, t_bool],
    "smtEqString": [t_string, t_string, t_bool],
    "smtNeqInt": [t_int, t_int, t_bool],
    "smtNeqFloat": [t_float, t_float, t_bool],
    "smtNeqBool": [t_float, t_float, t_bool],
    "smtNeqString": [t_string, t_string, t_bool],
    "smtNot": [t_bool, t_bool],
    "smtLeqInt": [t_int, t_int, t_bool],
    "smtLeqFloat": [t_float, t_float, t_bool],
    "smtLtInt": [t_int, t_int, t_bool],
    "smtLtFloat": [t_float, t_float, t_bool],
    "smtAnd": [t_bool, t_bool, t_bool],
    "smtOr": [t_bool, t_bool, t_bool],
    "smtPlusInt": [t_int, t_int, t_int],
    "smtMinusInt": [t_int, t_int, t_int],
    "smtMultInt": [t_int, t_int, t_int],
    "smtDivInt": [t_int, t_int, t_int],
    "smtModInt": [t_int, t_int, t_int],
    "smtPlusFloat": [t_float, t_float, t_float],
    "smtMinusFloat": [t_float, t_float, t_float],
    "smtMultFloat": [t_float, t_float, t_float],
    "smtDivFloat": [t_float, t_float, t_float],
    "smtImplies": [t_bool, t_bool, t_bool],
}

smt_function_translation: dict[str, list[str]] = {
    "==": ["smtEqBool", "smtEqInt", "smtEqFloat", "smtEqString"],
    "!=": ["smtNeqBool", "smtNeqInt", "smtNeqFloat", "smtNeqString"],
    "!": ["smtNot"],
    "<": ["smtLeqInt", "smtLeqFloat"],
    "<=": ["smtLtInt", "smtLtFloat"],
    "&&": ["smtAnd"],
    "||": ["smtOr"],
    "+": ["smtPlusInt", "smtPlusFloat"],
    "-": ["smtMinusInt", "smtMinusFloat"],
    "*": ["smtMultInt", "smtMultFloat"],
    "/": ["smtDivInt", "smtDivFloat"],
    "%": ["smtModInt"],
    "-->": ["smtImplies"],
}

base_functions: dict[str, Any] = {
    "==": lambda x, y: x == y,
    "!=": lambda x, y: x != y,
    "<": lambda x, y: x < y,
    "<=": lambda x, y: x <= y,
    ">": lambda x, y: x > y,
    ">=": lambda x, y: x >= y,
    "!": lambda x: Not(x),
    "&&": lambda x, y: And(x, y),
    "||": lambda x, y: Or(x, y),
    "+": lambda x, y: x + y,
    "-": lambda x, y: x - y,
    "*": lambda x, y: x * y,
    "/": lambda x, y: x / y,
    "%": lambda x, y: x % y,
    "-->": lambda x, y: Implies(x, y),
}


@dataclass
class SMTContext:
    sorts: list[str]
    functions: dict[str, AbstractionType]
    variables: dict[str, BaseType]
    premises: list[LiquidTerm]

    def with_sort(self, name: Name) -> SMTContext:
        return SMTContext(self.sorts + [str(name)], self.functions, self.variables, self.premises)

    def with_function(self, name: Name, ty: AbstractionType) -> SMTContext:
        return SMTContext(self.sorts, {**self.functions, str(name): ty}, self.variables, self.premises)

    def with_var(self, name: Name, ty: BaseType) -> SMTContext:
        return SMTContext(self.sorts, self.functions, {**self.variables, str(name): ty}, self.premises)

    def with_premise(self, p: LiquidTerm) -> SMTContext:
        return SMTContext(self.sorts, self.functions, self.variables, self.premises + [p])


@dataclass(init=False)
class CanonicConstraint:
    """Represents SMT-valid constraints."""

    sorts: list[str]
    functions: dict[str, AbstractionType]
    variables: dict[str, BaseType]
    premise: LiquidTerm
    conclusion: LiquidTerm

    def __init__(self, ctx: SMTContext, pos: LiquidTerm):
        self.sorts = ctx.sorts
        self.functions = ctx.functions
        self.variables = ctx.variables
        self.premise = reduce(mk_liquid_and, ctx.premises, LiquidLiteralBool(True))
        self.conclusion = pos


def rename_constraint(c: Constraint, old_name: Name, new_name: Name) -> Constraint:
    """Renames a binder within the constraint, to make it is unique."""
    match c:
        case LiquidConstraint(expr):
            nexpr = substitution_in_liquid(expr, LiquidVar(new_name), old_name)
            return LiquidConstraint(expr=nexpr)
        case Conjunction(c1, c2):
            return Conjunction(rename_constraint(c1, old_name, new_name), rename_constraint(c2, old_name, new_name))
        case Implication(name, base, pred, seq):
            if name == new_name:
                return c
            else:
                npred = substitution_in_liquid(pred, LiquidVar(new_name), old_name)
                nseq = rename_constraint(seq, old_name, new_name)
                return Implication(name, base, npred, nseq)
        case UninterpretedFunctionDeclaration(name, absty, seq):
            nseq = rename_constraint(seq, old_name, new_name)
            return UninterpretedFunctionDeclaration(name, absty, nseq)
        case _:
            assert False, f"Unexpected case {c} ({type(c)})"


def flatten(c: Constraint, ctx: SMTContext | None = None) -> Generator[CanonicConstraint]:
    """Flattens a constraint into a list of SMT-valid constraints."""
    if ctx is None:
        ctx = SMTContext(["Top"], {}, {}, [])
    match c:
        case LiquidConstraint(expr):
            yield CanonicConstraint(ctx, expr)
        case Conjunction(c1, c2):
            yield from flatten(c1, ctx)
            yield from flatten(c2, ctx)
        case Implication(oname, base, pred, seq):
            name = Name(oname.name, fresh_counter.fresh())
            pred = substitution_in_liquid(pred, LiquidVar(name), oname)
            seq = rename_constraint(seq, oname, name)
            match base:
                case BaseType(iname):
                    pass
                case TypeVar(iname):
                    base = BaseType(iname)
                case TypeConstructor(iname, args):
                    mangle_name = str(iname) + "_" + "_".join(str(a) for a in args)
                    nname = Name(mangle_name, fresh_counter.fresh())
                    base = BaseType(nname)
                case _:
                    assert False, f"{base} ({type(base)}) is not a base type."
            yield from flatten(seq, ctx.with_var(name, base).with_premise(pred))
        case UninterpretedFunctionDeclaration(name, ty, seq):
            assert isinstance(c, UninterpretedFunctionDeclaration)
            yield from flatten(seq, ctx.with_function(name, ty))
        case _:
            assert False, f"Cannot flatten {c}."


s = Solver()
(s.set(timeout=200),)


def smt_valid(constraint: Constraint) -> bool:
    """Verifies if a constraint is true using Z3."""
    n = 0
    for c in flatten(constraint):
        n += 1
        s.push()

        # TODO now: Add monomorphic, uncurried functions here
        try:
            smt_c = translate(c)
        except ZeroDivisionError:
            continue
        if smt_c is False:
            continue
        s.add(smt_c)
        result = s.check()
        s.pop()
        if result == sat:
            return False
        elif result == unknown:
            return False

    return True


def type_of_variable(variables: list[tuple[str, Any]], name: str) -> Any:
    for na, ref in reversed(variables):
        if na == name:
            return ref
    vars = ", ".join([x[0] for x in variables])
    logger.error(f"No variable {name} in the context: {vars}")
    assert False


sort_cache: dict[str, SortRef] = {}


def mk_vars(variables: dict[str, BaseType], sorts: dict[str, SortRef]) -> dict[str, Any]:
    return {name: make_variable(name, base) for name, base in variables.items()}


def get_sort(base: Type) -> SortRef:
    match base:
        case Top() | BaseType(Name("Top", _)):
            return DeclareSort("Top")
        case BaseType(Name("Int", _)):
            return IntSort()
        case BaseType(Name("Bool", _)):
            return BoolSort()
        case BaseType(Name("Float", _)):
            return Float64()
        case BaseType(Name("String", _)):
            return StringSort()
        case BaseType(name):
            return IntSort()
            # This will be reenable once we have typeclasses
            # if name not in sort_cache:
            #     sort_cache[name] = DeclareSort(name)
            # return sort_cache[name]
        case TypeVar(name):
            assert False, f"TypeVar {name} should not be used in SMT solver."
        case _:
            raise Exception(f"SMT sort of {base} not implemented.")


def unrefine_type(base: Type):
    """Removes refinements from type."""
    match base:
        case RefinedType(_, ty, _):
            return ty
        case AbstractionType(name, aty, rty):
            return AbstractionType(name, unrefine_type(aty), unrefine_type(rty))
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(name, kind, unrefine_type(body))
        case TypeConstructor(name, args):
            return TypeConstructor(name, [unrefine_type(a) for a in args])

        case _:
            return base


def uncurry(base: AbstractionType) -> tuple[list[BaseType], BaseType]:
    current: Type = unrefine_type(base)
    inputs = []
    while isinstance(current, AbstractionType):
        match current.var_type:
            case BaseType(_):
                inputs.append(current.var_type)
            case Top():
                inputs.append(t_unit)
            case TypeVar(name):
                inputs.append(BaseType(name))
            case _:
                assert False, f"Unknown SMT type {current.var_type} in {base}."
        current = current.type

    if isinstance(current, Top):
        current = t_unit
    assert isinstance(current, BaseType)
    return (inputs, current)


def make_variable(name: str, base: BaseType | AbstractionType | Top) -> Any:
    match base:
        case Top():
            return Const(name, get_sort(base))
        case BaseType(Name("Int", _)):
            return Int(name)
        case BaseType(
            Name(
                "Bool",
            )
        ):
            return Bool(name)
        case BaseType(Name("Float", _)):
            fpsort = FPSort(8, 24)
            return FP(name, fpsort)
        case BaseType(Name("String", _)):
            return String(name)
        case BaseType(_):
            return Int(name)
            # TODO: we always use int, in the case of a typevar.
            # return Const(name, get_sort(base))
        case TypeVar(_):
            return Int(name)
        case AbstractionType(_, _, _):
            if name in base_functions:
                return base_functions[name]
            else:
                input_types, output_type = uncurry(base)
                args = [get_sort(x) for x in input_types] + [get_sort(output_type)]
                return Function(name, *args)
        case _:
            assert False, f"No var: {name}, with base {base} of type {type(base)}"


def translate_liq(t: LiquidTerm, variables: dict[str, Any]):
    match t:
        case LiquidLiteralBool(b):
            return b
        case LiquidLiteralInt(i):
            return i
        case LiquidLiteralFloat(f):
            return f
        case LiquidLiteralString(s):
            return s
        case LiquidVar(name):
            return variables[str(name)]
        case LiquidHornApplication(name, args):
            assert False, "LiquidHornApplication should not get to SMT solver!"
        case LiquidApp(fun_name, args):
            fun = base_functions.get(fun_name.name, variables.get(str(fun_name), None))
            assert fun is not None, f"Function {fun_name} not found." + str(variables)
            args = [translate_liq(a, variables) for a in args]
            try:
                return fun(*args)
            except Z3Exception as e:
                raise e

        case _:
            assert False, f"Cannot translate {t}."


def mk_sorts(sorts: list[str]) -> dict[str, SortRef]:
    return {name: get_sort(BaseType(Name(name, 0))) for name in sorts}


def mk_funs(functions: dict[str, AbstractionType], sorts: dict[str, SortRef]) -> dict[str, Any]:
    funs = {}
    for name, ty in functions.items():
        input_types, output_type = uncurry(ty)
        args = [sorts.get(str(x), get_sort(x)) for x in input_types] + [
            sorts.get(str(output_type), get_sort(output_type))
        ]
        funs[name] = Function(name, *args)
    return funs


def translate(
    c: CanonicConstraint,
) -> BoolRef | bool:
    sorts = mk_sorts(c.sorts)
    functions = mk_funs(c.functions, sorts)
    variables = mk_vars(c.variables, sorts)
    e1 = translate_liq(c.premise, variables | functions)
    e2 = translate_liq(c.conclusion, variables | functions)
    if isinstance(e1, bool) and isinstance(e2, bool):
        return e1 and not e2
    return And(e1, Not(e2))
