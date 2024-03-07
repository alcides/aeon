"""Meta-programming code for optimization-related decorators."""

from typing import Any

from aeon.core.terms import Term, Var
from aeon.core.types import BaseType
from aeon.decorators.api import Metadata
from aeon.sugar.program import Definition


def raise_decorator_error(name: str) -> None:
    raise Exception(f"Exception in decorator named {name}.")


def metadata_update(metadata: Metadata, fun: Definition, aux_dict: dict[str, Any] = None) -> Metadata:
    if not aux_dict:
        aux_dict = {}
    if fun.name in metadata.keys():
        metadata[(str(fun.name))].update(aux_dict)
    else:
        metadata[(str(fun.name))] = aux_dict
    return metadata


def minimize_int(
    args: list[Term], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1, "minimize_int decorator expects a single argument"

    n_decorators = len(metadata.get(fun.name, {}).get("minimize_int", []))

    minimize_function_name = f"__internal__minimize_int_{fun.name}_{n_decorators}"
    minimize_function = Definition(name=minimize_function_name, args=[], type=BaseType("Int"), body=args[0])

    metadata = metadata_update(
        metadata, fun, {"minimize_int": metadata.get(fun.name, {}).get("minimize_int", []) + [minimize_function]}
    )
    return fun, [minimize_function], metadata


def minimize_float(
    args: list[Term], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1, "minimize_float decorator expects a single argument"

    n_decorators = len(metadata.get(fun.name, {}).get("minimize_float", []))
    minimize_function_name = f"__internal__minimize_float_{fun.name}_{n_decorators}"
    minimize_function = Definition(name=minimize_function_name, args=[], type=BaseType("Float"), body=args[0])

    metadata = metadata_update(
        metadata, fun, {"minimize_float": metadata.get(fun.name, {}).get("minimize_float", []) + [minimize_function]}
    )
    return fun, [minimize_function], metadata


def multi_minimize_float(
    args: list[Term], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1, "multi_minimize_float decorator expects a single argument"

    n_decorators = len(metadata.get(fun.name, {}).get("multi_minimize_float", []))
    minimize_function_name = f"__internal__multi_minimize_float_{fun.name}_{n_decorators}"
    minimize_function = Definition(name=minimize_function_name, args=[], type=BaseType("List"), body=args[0])

    metadata = metadata_update(
        metadata,
        fun,
        {"multi_minimize_float": metadata.get(fun.name, {}).get("multi_minimize_float", []) + [minimize_function]},
    )
    return fun, [minimize_function], metadata


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
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata
