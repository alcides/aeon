"""Meta-programming code for optimization-related decorators."""

import aeon.synthesis_grammar.grammar as grammar
from aeon.core.terms import Term
from aeon.core.types import BaseType
from aeon.sugar.program import Definition
from aeon.synthesis_grammar.utils import fitness_function_name_for


def minimize_int(args: list[Term], fun: Definition) -> tuple[Definition, list[Definition]]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1
    fitness_function = Definition(name=fitness_function_name_for(fun.name), args=[], type=BaseType("Int"), body=args[0])
    return fun, [fitness_function]


def minimize_float(args: list[Term], fun: Definition) -> tuple[Definition, list[Definition]]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1
    fitness_function = Definition(
        name=fitness_function_name_for(fun.name),
        args=[],
        type=BaseType("Float"),
        body=args[0],
    )
    return fun, [fitness_function]


def multi_minimize_float(args: list[Term], fun: Definition) -> tuple[Definition, list[Definition]]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1
    fitness_function = Definition(
        name=fitness_function_name_for(fun.name),
        args=[],
        type=BaseType("List"),
        body=args[0],
    )
    return fun, [fitness_function]


def ignore(args: list[Term], fun: Definition) -> tuple[Definition, list[Definition]]:
    # @grammar_skip
    """This decorator expects a zero argument .

    It does not modify the original definition. It makes sure that no
    grammar node is generated from this function.
    """
    assert len(args) == 0
    grammar.internal_functions.append(fun.name)
    # internal_function = Definition(name=internal_name_for(fun.name), args=fun.args, type=fun.type, body=fun.body)
    return fun, []
