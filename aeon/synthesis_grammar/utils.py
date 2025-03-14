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


def fitness_function_name_for(fun_name: str) -> str:
    return f"__internal__fitness_function_{fun_name}"


prelude_ops: list[str] = ["print", "native_import", "native"]

internal_functions: list[str] = []

text_to_aeon_prelude_ops: dict[str, str] = {v: k for k, v in aeon_prelude_ops_to_text.items()}

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
