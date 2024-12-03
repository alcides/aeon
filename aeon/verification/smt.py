from __future__ import annotations

from dataclasses import dataclass
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
from z3.z3 import ForAll
from z3.z3 import FPSort
from z3.z3 import Float64
from z3.z3 import Implies
from z3.z3 import IntSort
from z3.z3 import Not
from z3.z3 import Or
from z3.z3 import String
from z3.z3 import StringSort

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidHornApplication
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, Bottom, RefinedType, Top, TypePolymorphism, TypeConstructor
from aeon.core.types import BaseType
from aeon.core.types import Type
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.vcs import UninterpretedFunctionDeclaration

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
class CanonicConstraint:
    binders: list[tuple[str, BaseType | AbstractionType | Bottom | Top]]
    pre: LiquidTerm
    pos: LiquidTerm

    def __repr__(self):
        return f"\\forall {self.binders}, {self.pre} => {self.pos}"


def rename_constraint(c: Constraint, old_name: str,
                      new_name: str) -> Constraint:
    """Renames a binder within the constraint, to make it is unique."""
    if isinstance(c, Conjunction):
        return Conjunction(rename_constraint(c.c1, old_name, new_name),
                           rename_constraint(c.c2, old_name, new_name))
    elif isinstance(c, Implication):
        # If it shadows, leave it.
        if c.name == new_name:
            return c
        else:
            npred = substitution_in_liquid(c.pred, LiquidVar(new_name),
                                           old_name)
            nseq = rename_constraint(c.seq, old_name, new_name)
            return Implication(c.name, c.base, npred, nseq)
    elif isinstance(c, LiquidConstraint):
        nexpr = substitution_in_liquid(c.expr, LiquidVar(new_name), old_name)
        return LiquidConstraint(expr=nexpr)
    elif isinstance(c, UninterpretedFunctionDeclaration):
        # If it shadows, leave it.
        if c.name == new_name:
            return c
        else:
            nseq = rename_constraint(c.seq, old_name, new_name)
            return UninterpretedFunctionDeclaration(c.name, c.type, nseq)
    else:
        assert False


def get_new_name(name: str, used_vars: list[str]) -> None | str:
    """If a new name for a variable is needed, return it, otherwise return
    None."""
    if name not in used_vars:
        return None
    while name in used_vars:
        name = name + "_"
    return name


def flatten(c: Constraint,
            used_vars: list[str]) -> Generator[CanonicConstraint, None, None]:
    if isinstance(c, Conjunction):
        yield from flatten(c.c1, used_vars)
        yield from flatten(c.c2, used_vars)
    elif isinstance(c, Implication):
        name = get_new_name(c.name, used_vars)
        if name:
            c = rename_constraint(c, c.name, name)
            assert isinstance(c, Implication)
        else:
            name = c.name
        for sub in flatten(c.seq, used_vars + [name]):
            yield CanonicConstraint(
                binders=[(name, c.base)] + sub.binders,
                pre=mk_liquid_and(sub.pre, c.pred),
                pos=sub.pos,
            )
    elif isinstance(c, LiquidConstraint):
        yield CanonicConstraint(binders=[],
                                pre=LiquidLiteralBool(True),
                                pos=c.expr)
    elif isinstance(c, UninterpretedFunctionDeclaration):
        name = get_new_name(c.name, used_vars)
        if name:
            c = rename_constraint(c, c.name, name)
            assert isinstance(c, UninterpretedFunctionDeclaration)
        else:
            name = c.name
        for sub in flatten(c.seq, used_vars):
            yield CanonicConstraint(
                binders=[(c.name, c.type)] + sub.binders,
                pre=sub.pre,
                pos=sub.pos,
            )
    else:
        assert False


s = Solver()
(s.set(timeout=200), )
# TODO
# (==[Top] x 3) is happily generated by Aeon. We need to go over all basic functions, and bring bottom down to Int, for all applications of native applications.

assert False


def smt_valid(constraint: Constraint,
              foralls: None | list[tuple[str, Any]] = None) -> bool:
    """Verifies if a constraint is true using Z3."""
    if foralls is None:
        foralls = []
    forall_vars = [(f[0], make_variable(f[0], f[1])) for f in foralls
                   if isinstance(f[1], BaseType)]
    cons: list[CanonicConstraint] = list(flatten(constraint, []))
    for c in cons:
        s.push()

        # TODO now: Add monomorphic, uncurried functions here
        smt_c = translate(c, extra=forall_vars)
        for _, v in forall_vars:
            smt_c = ForAll(v, smt_c)
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


sort_cache = {}


def get_sort(base: Type) -> Any:
    match base:
        case Bottom():
            return DeclareSort("Bottom")
        case Top():
            return DeclareSort("Top")
        case BaseType("Int"):
            return IntSort()
        case BaseType("Bool"):
            return BoolSort()
        case BaseType("Float"):
            return Float64()
        case BaseType("String"):
            return StringSort()
        case BaseType("TypeVarPlaceHolder"):
            return IntSort()  # TODO
        case BaseType("TypeConstructorPlaceHolder"):
            return IntSort()  # TODO
        case BaseType(name):
            if name not in sort_cache:
                sort_cache[name] = DeclareSort(name)
            return sort_cache[name]
        case _:
            raise Exception(f"SMT sort of {base} not implemented.")


def unrefine_type(base: Type):
    """Removes refinements from type."""
    match base:
        case RefinedType(_, ty, _):
            return ty
        case AbstractionType(name, aty, rty):
            return AbstractionType(name, unrefine_type(aty),
                                   unrefine_type(rty))
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(name, kind, unrefine_type(body))
        case _:
            return base


def uncurry(
    base: AbstractionType
) -> tuple[list[BaseType | Top | Bottom], BaseType | Top | Bottom]:
    current: Type = unrefine_type(base)
    inputs = []
    while isinstance(current, AbstractionType):
        vtype = current.var_type
        if isinstance(vtype, TypeConstructor):
            vtype = BaseType("TypeConstructorPlaceHolder")
        assert isinstance(vtype, BaseType) or isinstance(
            vtype, Top) or isinstance(vtype, Bottom)
        inputs.append(vtype)
        current = current.type
    assert isinstance(current, BaseType) or isinstance(
        current, Top) or isinstance(current, Bottom)
    return (inputs, current)


def make_variable(name: str,
                  base: BaseType | AbstractionType | Top | Bottom) -> Any:
    match base:
        case Bottom() | Top():
            return Const(name, get_sort(base))
        case BaseType("Int"):
            return Int(name)
        case BaseType("Bool"):
            return Bool(name)
        case BaseType("Float"):
            fpsort = FPSort(8, 24)
            return FP(name, fpsort)
        case BaseType("String"):
            return String(name)
        case BaseType(_):
            return Const(name, get_sort(base))
        case AbstractionType(_, _, _):
            if name in base_functions:
                return base_functions[name]
            else:
                input_types, output_type = uncurry(base)
                args = [get_sort(x)
                        for x in input_types] + [get_sort(output_type)]
                return Function(name, *args)
        case _:
            logger.error(
                f"No var: {name}, with base {base} of type {type(base)}")
            assert False


def translate_liq(t: LiquidTerm, variables: list[tuple[str, Any]]):
    if isinstance(t, LiquidLiteralBool):
        return t.value
    elif isinstance(t, LiquidLiteralInt):
        return t.value
    elif isinstance(t, LiquidLiteralFloat):
        return t.value
    elif isinstance(t, LiquidLiteralString):
        return t.value
    elif isinstance(t, LiquidVar):
        return type_of_variable(variables, t.name)
    elif isinstance(t, LiquidHornApplication):
        assert False  # LiquidHoles should not get to SMT solver!
    elif isinstance(t, LiquidApp):
        f = None
        if t.fun in base_functions:
            f = base_functions[t.fun]
        else:
            for v in variables:
                if v[0] == t.fun:
                    f = v[1]
        if f is None:
            logger.error(f"Failed to find function {t.fun}.")
            assert False
        args = [translate_liq(a, variables) for a in t.args]
        return f(*args)
    assert False


def uncurry_named(
        base: AbstractionType) -> tuple[list[tuple[str, Type]], Type]:
    current = base
    inputs = []
    while isinstance(current, AbstractionType):
        match current.var_type:
            case TypeConstructor():
                vtype = BaseType("TypeConstructorPlaceHolder")
            case other:
                vtype = other

        inputs.append((current.var_name, vtype))
        current = current.type
    return (inputs, current)


def reflect_from_type(abs: AbstractionType, f: Function,
                      other_vars: list[tuple[str, Any]]):
    inputs, output = uncurry_named(abs)

    variables = []
    for name, ty in inputs:
        match ty:
            case BaseType(_) | Top() | Bottom():
                variables.append((name, make_variable(name, ty)))
            case RefinedType(_, tty, _):
                variables.append((name, make_variable(name, tty)))
                # TODO: Ignore refinement here?
            case _:
                assert False

    body: LiquidTerm = LiquidLiteralBool(True)
    match output:
        case RefinedType(x, tty, ref):
            args = [v[1] for v in variables]
            expr = f(args)
            body = translate_liq(ref, other_vars + variables + [(x, expr)])
        case _:
            pass
    return ForAll([x[1] for x in variables], body)


def translate(
    c: CanonicConstraint,
    extra=list[tuple[str, Any]],
) -> BoolRef | bool:
    variables = [
        (name, make_variable(name, base)) for (name, base) in c.binders[::-1]
        if isinstance(base, BaseType) or isinstance(base, AbstractionType)
        or isinstance(base, Top) or isinstance(base, Bottom)
    ] + extra

    def get_fun(variables, name):
        for fname, f in variables:
            if fname == name:
                return f
        assert False

    reflections = [
        reflect_from_type(base, get_fun(variables, name), variables)
        for (name, base) in c.binders[::-1]
        if isinstance(base, AbstractionType)
    ]
    e1 = translate_liq(c.pre, variables)
    e2 = translate_liq(c.pos, variables)
    if isinstance(e1, bool) and isinstance(e2, bool):
        return e1 and not e2
    if reflections:
        return And(*reflections + [e1, Not(e2)])
    return And(e1, Not(e2))
