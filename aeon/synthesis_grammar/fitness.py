from __future__ import annotations

from aeon.annotations import annotations
from aeon.core.terms import Term
from aeon.core.types import BaseType
from aeon.core.types import Type
from aeon.sugar.program import Definition

real_eval = eval


class Fitness:
    definition: Definition
    minimize: list[bool]

    def __init__(self, definition: Definition, minimize: list[bool]):
        self.definition = definition
        self.minimize = minimize

    def get_minimize(self):
        if len(self.minimize) == 1:
            return self.minimize[0]
        else:
            return self.minimize


def extract_fitness_from_definition(d: Definition) -> Fitness:
    macro_list = d.macros
    minimize_list = []
    if any(macro.name in ("minimize", "maximize") for macro in macro_list):
        minimize_list = [
            True if m.name == "minimize" else False for m in macro_list if m.name in ["minimize", "maximize"]
        ]
    elif any(macro.name in ("multi_maximize", "multi_minimize") for macro in macro_list):
        assert len(macro_list) == 1
        multi_annotation = macro_list[0]
        minimize_list_length = 200  # TODO: get this value dynamically
        minimize = True if multi_annotation.name == "multi_minimize" else False
        minimize_list = [minimize for _ in range(minimize_list_length)]
    assert len(minimize_list) > 0
    expression_list = [(m.name, m.expressions) for m in macro_list]
    fitness_args = d.args

    return Fitness(minimize_list, fitness_args, expression_list)


def transform_fitness_into_definition(f: Fitness) -> Definition:
    fitness_return_type = BaseType("Float") if len(f.minimize) == 1 else BaseType("List")
    d = None
    # TODO: adapt this to work with more than one expression
    for expression in f.expressions:
        annotation_func = getattr(annotations, expression[0])
        d = Definition("fitness", [], fitness_return_type, annotation_func(expression[1]))

    assert d, "Definition Term not defined"
    return d
