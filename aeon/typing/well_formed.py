from aeon.typing.liquid import type_infer_liquid
from aeon.core.types import (
    Type,
    BaseType,
    TypeVar,
    AbstractionType,
    RefinedType,
    t_bool,
)
from aeon.typing.context import TypingContext


def wellformed(ctx: TypingContext, t: Type) -> bool:
    if isinstance(t, BaseType):
        return True
    elif isinstance(t, TypeVar):
        return True  # TODO: var context
    elif isinstance(t, AbstractionType):
        return wellformed(ctx, t.var_type) and wellformed(
            ctx.with_var(t.var_name, t.var_type), t.type
        )
    elif isinstance(t, RefinedType):
        return (
            wellformed(ctx, t.type)
            and type_infer_liquid(ctx.with_var(t.name, t.type), t.refinement) == t_bool
        )
    assert False
