from typing import Any
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Type
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import Top


def mangle_term(x: Any) -> str:
    """Mangles the liquid/non-liquid term used in a refined type."""
    return (
        str(x)
        .replace(" ", "_")
        .replace("(", "__oparens__")
        .replace(")", "__cparens__")
        .replace("<", "__lt__")
        .replace("<=", "__lte__")
        .replace(">", "__gt__")
        .replace(">", "__gte__")
        .replace("==", "__eq__")
        .replace("!=", "__neq__")
        .replace("&&", "__and__")
        .replace("||", "__or__")
        .replace("+", "__plus__")
        .replace("-", "__minus__")
        .replace("*", "__times__")
        .replace("/", "__div__")
        .replace("%", "__mod__")
    )


def mangle_type(ty: Type) -> str:
    """Mangles the Aeon Type name, to be a valid Python name."""
    match ty:
        case BaseType(name):
            return f"æ{name}"
        case RefinedType(name, ty, ref):
            ref2 = substitution_in_liquid(ref, LiquidVar("__self__"), name)
            return f"_{mangle_type(ty)}_{mangle_term(ref2)}"
        case AbstractionType(var_name, var_type, type):
            ty1 = mangle_type(var_type)
            ty2 = mangle_type(substitution_in_type(type, Var("__self__"), var_name))
            return f"{ty1}_arrow_{ty2}"
        case Top():
            return "top"
        case Bottom():
            return "bottom"
        case _:
            assert False
