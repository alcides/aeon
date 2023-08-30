from __future__ import annotations

from aeon.annotations import annotations
from aeon.core.terms import Term
from aeon.core.types import BaseType
from aeon.core.types import Type
from aeon.sugar.program import Definition
from aeon.sugar.program import Macro


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


def extract_fitness_from_synth(d: Definition) -> Fitness:
    fitness_args: list[tuple[str, Type]] = d.args
    macro_list: list[Macro] = d.macros

    minimize_list = []
    fitness_terms = []
    for macro in macro_list:
        annotation_func = getattr(annotations, macro.name)
        expr_term, minimize = annotation_func(macro.macro_args)

        if minimize is not None:
            add_to_list(minimize, minimize_list)
        add_to_list(expr_term, fitness_terms)

    assert len(minimize_list) > 0
    assert len(fitness_terms) > 0

    fitness_return_type = BaseType("Float") if len(minimize_list) == 1 else BaseType("List")

    fitness_function = generate_definition(fitness_args, fitness_return_type, fitness_terms)

    return Fitness(fitness_function, minimize_list)


def add_to_list(item: list[bool] | bool, my_list: list[bool]):
    try:
        my_list += item if isinstance(item, list) else [item]
    except TypeError as e:
        raise TypeError(f"An error occurred while adding to the list: {e}")

    return my_list


def generate_definition(
    fitness_args: list[tuple[str, Type]],
    fitness_return_type: BaseType,
    fitness_terms: list[Term],
) -> Definition:
    if len(fitness_terms) == 1:
        return Definition(name="fitness", args=[], type=fitness_return_type, body=fitness_terms[0])
    else:
        raise Exception("Not yet supported")
