from geneticengine.grammar.metahandlers.floats import FloatRange
from geneticengine.grammar.metahandlers.ints import IntRange
from geneticengine.grammar.metahandlers.strings import StringSizeBetween

from aeon.core.liquid import LiquidLiteralInt, LiquidLiteralString, LiquidLiteralFloat


def fitness_function_name_for(fun_name: str) -> str:
    return f"__internal__fitness_function_{fun_name}"


prelude_ops: list[str] = ["print", "native_import", "native"]

internal_functions: list[str] = []

aeon_prelude_ops_to_text: dict[str, str] = {
    "%": "mod",
    "/": "div",
    "*": "mult",
    "-": "sub",
    "+": "add",
    "%.": "mod_f",
    "/.": "div_f",
    "*.": "mult_f",
    "-.": "sub_f",
    "+.": "add_f",
    ">=": "greater_equal",
    ">": "greater_than",
    "<=": "less_equal",
    "<": "less_than",
    "!=": "not_equal",
    "==": "equal",
    "&&": "and",
    "||": "or",
}
text_to_aeon_prelude_ops = {v: k for k, v in aeon_prelude_ops_to_text.items()}

grammar_base_types = ["t_Float", "t_Int", "t_String", "t_Bool"]

aeon_to_python_types = {"Int": int, "Bool": bool, "String": str, "Float": float}

aeon_to_gengy_metahandlers = {"Int": IntRange, "String": StringSizeBetween, "Float": FloatRange}

aeon_to_liquid_terms = {"Int": LiquidLiteralInt, "String": LiquidLiteralString, "Float": LiquidLiteralFloat}
