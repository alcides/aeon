"""Meta-programming code for optimization-related decorators."""

from aeon.core.terms import Term, Var
from aeon.core.types import BaseType
from aeon.decorators.api import Metadata
from aeon.sugar.program import Definition
from aeon.synthesis_grammar.utils import fitness_function_name_for


def raise_decorator_error(name: str) -> None:
    raise Exception(f"Exception in decorator named {name}.")


def minimize_int(
    args: list[Term], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1
    fitness_function = Definition(name=fitness_function_name_for(fun.name), args=[], type=BaseType("Int"), body=args[0])
    return fun, [fitness_function], metadata


def minimize_float(
    args: list[Term], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
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
    return fun, [fitness_function], metadata


def multi_minimize_float(
    args: list[Term], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
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
    return fun, [fitness_function], metadata


def syn_ignore(args: list[Term], fun: Definition, metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a zero argument .

    It does not modify the original definition. It makes sure that no
    grammar node is generated from this function.
    """
    assert len(args) != 0

    # TODO How can I verify if the function is in the context?
    def get_var_name(arg):
        if isinstance(arg, Var):
            return arg.name
        else:
            raise_decorator_error("syn_ignore")

    # rethink this
    aux_dict = {"syn_ignore": [get_var_name(arg) for arg in args]}
    assert isinstance(fun.name, str)
    if fun.name in metadata.keys():
        metadata[(str(fun.name))].update(aux_dict)
    else:
        metadata[(str(fun.name))] = aux_dict

    return fun, [], metadata
