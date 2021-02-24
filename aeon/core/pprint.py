from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import (
    Type,
    TypeVar,
    BaseType,
    AbstractionType,
    RefinedType,
    type_free_term_vars,
)


def pretty_print(t: Type) -> str:
    if isinstance(t, BaseType):
        return str(t)
    elif isinstance(t, TypeVar):
        return str(t)
    elif isinstance(t, AbstractionType):
        at = pretty_print(t.var_type)
        rt = pretty_print(t.type)
        if t.var_name in type_free_term_vars(at):
            return f"({t.var_name}:{at}) -> {rt}"
        else:
            return f"{at} -> {rt}"
    elif isinstance(t, RefinedType):
        it = pretty_print(t.type)
        if t.refinement == LiquidLiteralBool(True):
            return it
        else:
            return f"{{{t.name}:{it} | {t.refinement}}}"
