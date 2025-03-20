from aeon.core.liquid import LiquidApp, LiquidTerm, LiquidVar
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Type
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.pprint import aeon_prelude_ops_to_text


def mangle_liquid_term(refinement: LiquidTerm) -> str:
    match refinement:
        case LiquidApp(fun, args):
            fun_name = aeon_prelude_ops_to_text.get(fun, fun)
            args_text = "__comma__".join([mangle_liquid_term(t) for t in args])
            return f"__opar__{fun_name}__{args_text}__cpar__"
        case _:
            return str(refinement)


def mangle_var(name: str) -> str:
    """Mangles the name of variable, so it is a valid Python identifier."""
    return aeon_prelude_ops_to_text.get(name, name)


def mangle_type(ty: Type) -> str:
    """Mangles the Aeon Type name, to be a valid Python name."""
    match ty:
        case BaseType(name):
            return f"æ{name}"
        case RefinedType(name, ty, ref):
            ref2 = substitution_in_liquid(ref, LiquidVar("__self__"), name)
            return f"_{mangle_type(ty)}_{mangle_liquid_term(ref2)}"
        case AbstractionType(var_name, var_type, type):
            ty1 = mangle_type(var_type)
            ty2 = mangle_type(
                substitution_in_type(type, Var("__self__"), var_name))
            return f"{ty1}_arrow_{ty2}"
        case Top():
            return "Top"
        case _:
            assert False, f"Unsupported {ty}"
