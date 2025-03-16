from typing import Type

from geneticengine.grammar.metahandlers.base import MetaHandlerGenerator
from geneticengine.grammar.metahandlers.floats import FloatRange
from geneticengine.grammar.metahandlers.ints import IntRange
from geneticengine.grammar.metahandlers.strings import StringSizeBetween
from geneticengine.representations.grammatical_evolution.dynamic_structured_ge import (
    DynamicStructuredGrammaticalEvolutionRepresentation,
)
from geneticengine.representations.grammatical_evolution.ge import GrammaticalEvolutionRepresentation
from geneticengine.representations.grammatical_evolution.structured_ge import (
    StructuredGrammaticalEvolutionRepresentation,
)
from geneticengine.representations.tree.treebased import TreeBasedRepresentation

from aeon.core.liquid import LiquidLiteralInt, LiquidLiteralString, LiquidLiteralFloat


def fitness_function_name_for(fun_name: str) -> str:
    return f"__internal__fitness_function_{fun_name}"


prelude_ops: list[str] = ["print", "native_import", "native"]

internal_functions: list[str] = []

aeon_prelude_ops_to_text = {
    "%": "mod",
    "/": "div",
    "*": "mul",
    "-": "sub",
    "+": "add",
    "%.": "modf",
    "/.": "divf",
    "*.": "mulf",
    "-.": "subf",
    "+.": "addf",
    ">=": "gte",
    ">": "gt",
    "<=": "lte",
    "<": "lt",
    "!=": "ne",
    "==": "eq",
    "&&": "and",
    "||": "or",
}
text_to_aeon_prelude_ops: dict[str, str] = {v: k for k, v in aeon_prelude_ops_to_text.items()}

grammar_base_types: list[str] = ["t_Float", "t_Int", "t_String", "t_Bool"]

aeon_to_python_types: dict[str, type] = {"Int": int, "Bool": bool, "String": str, "Float": float}

aeon_to_gengy_metahandlers: dict[str, MetaHandlerGenerator] = {
    "Int": IntRange,
    "String": StringSizeBetween,
    "Float": FloatRange,
}

aeon_to_liquid_terms: dict[str, Type[LiquidLiteralFloat | LiquidLiteralInt | LiquidLiteralString]] = {
    "Int": LiquidLiteralInt,
    "String": LiquidLiteralString,
    "Float": LiquidLiteralFloat,
}

representations = {
    "tree": TreeBasedRepresentation,
    "ge": GrammaticalEvolutionRepresentation,
    "sge": StructuredGrammaticalEvolutionRepresentation,
    "dsge": DynamicStructuredGrammaticalEvolutionRepresentation,
}

fitness_decorators = ["minimize_int", "minimize_float", "multi_minimize_float"]

gengy_default_config = {
    "seed": 123,
    "verbose": 2,
    "config_name": "DEFAULT",
    # Stopping criteria
    "timer_stop_criteria": True,
    "timer_limit": 60,
    # Recording
    "only_record_best_inds": True,
    # Representation
    "representation": "tree",
    "max_depth": 8,
    # Population and Steps
    "population_size": 20,
    "n_elites": 1,
    "novelty": 1,
    "probability_mutation": 0.1,
    "probability_crossover": 0.7,
    "tournament_size": 2,
}
