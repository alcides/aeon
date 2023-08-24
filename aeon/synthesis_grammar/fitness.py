from __future__ import annotations

from aeon.annotations import annotations
from aeon.core.terms import Term
from aeon.core.types import BaseType
from aeon.core.types import Type
from aeon.sugar.program import Definition


class Fitness:
    args: list[tuple[str, Type]]
    minimize: list[bool]
    expressions: list[tuple[str, Term]]

    def __init__(self, minimize, args, expressions):
        self.minimize = minimize
        self.args = args
        self.expressions = expressions

    def get_minimize(self):
        if len(self.minimize) == 1:
            return self.minimize[0]
        else:
            # TODO: handle multiobjective problem fitness
            return True


def extract_fitness_from_definition(d: Definition) -> Fitness:
    macros = d.macros
    minimize_list = [True if m.name == "minimize" else False for m in macros if m.name in ["minimize", "maximize"]]
    expression_list = [(m.name, m.expression) for m in macros]
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
