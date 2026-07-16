"""z3-py shims used by the SMT-based synthesis backends.

These build raw z3-py expressions for the synthesizer modules that issue
their own z3 queries (rather than going through the Rust ``smt_valid``).
They used to live in ``aeon/verification/smt.py`` but were moved here so
the verification layer can be 100% Rust-backed.

Used by:

* ``aeon/synthesis/modules/smt_synthesizer.py``
* ``aeon/synthesis/modules/tdsyn/smt_solve.py``
"""

from __future__ import annotations

from typing import Any

from z3 import Function
from z3 import Int
from z3 import StringVal
from z3.z3 import Bool
from z3.z3 import BoolSort
from z3.z3 import Const
from z3.z3 import DeclareSort
from z3.z3 import Implies
from z3.z3 import IntSort
from z3.z3 import RealSort
from z3.z3 import Not
from z3.z3 import Or
from z3.z3 import String
from z3.z3 import StringSort
from z3.z3 import SortRef
from z3.z3types import Z3Exception
from z3 import And, EmptySet, SetAdd, SetUnion, SetIntersect, SetDifference, IsMember, IsSubset, SetSort

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.types import (
    AbstractionType,
    LiquidHornApplication,
    Top,
    Type,
    TypeConstructor,
    TypeVar,
)
from aeon.utils.name import Name
from aeon.verification.smt import uncurry

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
    "Set_empty": EmptySet(IntSort()),
    "Set_sng": lambda x: SetAdd(EmptySet(IntSort()), x),
    "Set_cup": lambda a, b: SetUnion(a, b),
    "Set_cap": lambda a, b: SetIntersect(a, b),
    "Set_dif": lambda a, b: SetDifference(a, b),
    "Set_mem": lambda x, s: IsMember(x, s),
    "Set_sub": lambda a, b: IsSubset(a, b),
}


_sort_cache: dict[str, SortRef] = {}


def get_sort(base: Type) -> SortRef:
    match base:
        case Top() | TypeConstructor(Name("Top", _)):
            return IntSort()
        case TypeConstructor(Name("Int", _)):
            return IntSort()
        case TypeConstructor(Name("Bool", _)):
            return BoolSort()
        case TypeConstructor(Name("Float", _)):
            return RealSort()
        case TypeConstructor(Name("String", _)):
            return StringSort()
        case TypeConstructor(Name("Set", _)):
            return SetSort(IntSort())
        case TypeConstructor(name, _):
            sname = str(name)
            if sname[:1].isupper():
                if sname not in _sort_cache:
                    _sort_cache[sname] = DeclareSort(sname)
                return _sort_cache[sname]
            return IntSort()
        case TypeVar(name):
            assert False, f"TypeVar {name} should not be used in SMT solver."
        case _:
            raise Exception(f"SMT sort of {base} not implemented.")


def make_variable(name: str, base: TypeConstructor | AbstractionType | Top) -> Any:
    match base:
        case Top():
            return Int(name)
        case TypeConstructor(Name("Int", _)):
            return Int(name)
        case TypeConstructor(Name("Bool", _)):
            return Bool(name)
        case TypeConstructor(Name("Float", _), _):
            import z3

            return z3.Real(name)
        case TypeConstructor(Name("String", _)):
            return String(name)
        case TypeConstructor(Name("Set", _)):
            return Const(name, SetSort(IntSort()))
        case TypeConstructor(Name("Top", _)):
            return Int(name)
        case TypeConstructor(_, _):
            return Const(name, get_sort(base))
        case TypeVar(_):
            return Int(name)
        case AbstractionType(_, _, _):
            if name in base_functions:
                return base_functions[name]
            input_types, output_type = uncurry(base)
            args = [get_sort(x) for x in input_types] + [get_sort(output_type)]
            return Function(name, *args)
        case _:
            assert False, f"No var: {name}, with base {base}."


def translate_liq(t: LiquidTerm, variables: dict[str, Any]):
    match t:
        case LiquidLiteralBool(b):
            return b
        case LiquidLiteralInt(i):
            return i
        case LiquidLiteralFloat(f):
            return f
        case LiquidLiteralString(s):
            return StringVal(s)
        case LiquidVar(name):
            sname = str(name)
            if sname in variables:
                return variables[sname]
            if sname in base_functions:
                return base_functions[sname]
            raise KeyError(f"Variable {sname} not found in SMT context")
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
