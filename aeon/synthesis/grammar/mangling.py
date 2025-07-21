from aeon.core.liquid import LiquidApp, LiquidTerm, LiquidVar
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Type
from aeon.core.types import TypeConstructor
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.pprint import aeon_prelude_ops_to_text
from aeon.utils.name import Name


def mangle_name(name: Name) -> str:
    if name.id == 0:
        return name.name
    elif name.id == -1:
        return name.name + "_unknown"
    return name.name + "_" + str(name.id)


def mangle_liquid_term(refinement: LiquidTerm) -> str:
    match refinement:
        case LiquidApp(Name(fun, _), args):
            fun_name = aeon_prelude_ops_to_text.get(fun, fun)
            args_text = "__comma__".join([mangle_liquid_term(t) for t in args])
            return f"__opar__{fun_name}__{args_text}__cpar__"
        case _:
            return str(refinement)


def mangle_var(name: Name) -> str:
    """Mangles the name of variable, so it is a valid Python identifier."""
    return aeon_prelude_ops_to_text.get(name.name, mangle_name(name))


def mangle_type(ty: Type) -> str:
    """Mangles the Aeon Type name, to be a valid Python name."""
    match ty:
        case TypeConstructor(name, _):
            return f"æ{mangle_name(name)}"
        case RefinedType(name, ty, ref):
            ref2 = substitution_in_liquid(ref, LiquidVar(Name("__self__", 0)), name)
            return f"_{mangle_type(ty)}_{mangle_liquid_term(ref2)}"
        case AbstractionType(var_name, var_type, type):
            ty1 = mangle_type(var_type)
            ty2 = mangle_type(substitution_in_type(type, Var(Name("__self__", 0)), var_name))
            return f"{ty1}_arrow_{ty2}"
        case Top():
            return "Top"
        case _:
            assert False, f"Unsupported {ty}"
