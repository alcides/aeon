from typing import Type as TypingType

from geneticengine.grammar.metahandlers.base import MetaHandlerGenerator
from geneticengine.grammar.metahandlers.floats import FloatRange
from geneticengine.grammar.metahandlers.ints import IntRange
from geneticengine.grammar.metahandlers.strings import StringSizeBetween

from aeon.core.liquid import LiquidLiteralInt, LiquidLiteralString, LiquidLiteralFloat
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.core.types import Type
from aeon.core.pprint import aeon_prelude_ops_to_text

# Names that must never appear in synthesized terms.
SYNTHESIS_EXCLUDED_NAMES: frozenset[str] = frozenset({"native", "native_import", "print"})

prelude_ops: list[str] = sorted(SYNTHESIS_EXCLUDED_NAMES)

internal_functions: list[str] = []

text_to_aeon_prelude_ops: dict[str, str] = {v: k for k, v in aeon_prelude_ops_to_text.items()}


def _prelude_binding_names() -> frozenset[str]:
    from aeon.prelude.prelude import typing_vars

    return frozenset(n.name for n in typing_vars)


# Prelude operators and internal names tactics must not treat as hypotheses or
# call targets (``==`` is not a Boolean scrutinee; ``$`` is not a user value).
TACTIC_CONTEXT_EXCLUDED_NAMES: frozenset[str] = (
    SYNTHESIS_EXCLUDED_NAMES
    | _prelude_binding_names()
    | frozenset(aeon_prelude_ops_to_text.keys())
    | frozenset(text_to_aeon_prelude_ops.keys())
)

grammar_base_types: list[str] = ["t_Float", "t_Int", "t_String", "t_Bool"]

aeon_to_python_types: dict[str, TypingType] = {"Int": int, "Bool": bool, "String": str, "Float": float}

aeon_to_python: dict[Type, TypingType] = {
    t_bool: bool,
    t_int: int,
    t_string: str,
    t_float: float,
}

aeon_to_gengy_metahandlers: dict[Type, MetaHandlerGenerator] = {
    t_int: IntRange,
    t_string: StringSizeBetween,
    t_float: FloatRange,
}

aeon_to_liquid_terms: dict[str, TypingType[LiquidLiteralFloat | LiquidLiteralInt | LiquidLiteralString]] = {
    "Int": LiquidLiteralInt,
    "String": LiquidLiteralString,
    "Float": LiquidLiteralFloat,
}
