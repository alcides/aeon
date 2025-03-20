"""Meta-programming code for optimization-related decorators."""

from aeon.decorators.api import Metadata, metadata_update
from aeon.sugar.program import Definition, STerm, SVar
from aeon.sugar.stypes import SBaseType


def raise_decorator_error(name: str) -> None:
    raise Exception(f"Exception in decorator named {name}.")


def minimize_int(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1, "minimize_int decorator expects a single argument"

    n_decorators = len(metadata.get(fun.name, {}).get("minimize_int", []))

    minimize_function_name = f"__internal__minimize_int_{fun.name}_{n_decorators}"
    minimize_function = Definition(
        name=minimize_function_name,
        foralls=[],
        args=[],
        type=SBaseType("Int"),
        body=args[0],
    )

    metadata = metadata_update(
        metadata,
        fun,
        {
            "minimize_int":
            metadata.get(fun.name, {}).get("minimize_int", []) +
            [minimize_function],
        },
    )
    return fun, [minimize_function], metadata


def minimize_float(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert len(args) == 1, "minimize_float decorator expects a single argument"

    n_decorators = len(metadata.get(fun.name, {}).get("minimize_float", []))
    minimize_function_name = f"__internal__minimize_float_{fun.name}_{n_decorators}"
    minimize_function = Definition(
        name=minimize_function_name,
        foralls=[],
        args=[],
        type=SBaseType("Float"),
        body=args[0],
    )

    metadata = metadata_update(
        metadata,
        fun,
        {
            "minimize_float":
            metadata.get(fun.name, {}).get("minimize_float", []) +
            [minimize_function],
        },
    )
    return fun, [minimize_function], metadata


def multi_minimize_float(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    assert (len(args, ) == 1
            ), "multi_minimize_float decorator expects a single argument"

    n_decorators = len(
        metadata.get(fun.name, {}).get("multi_minimize_float", []), )
    minimize_function_name = f"__internal__multi_minimize_float_{fun.name}_{n_decorators}"
    minimize_function = Definition(
        name=minimize_function_name,
        foralls=[],
        args=[],
        type=SBaseType("List"),
        body=args[0],
    )

    metadata = metadata_update(
        metadata,
        fun,
        {
            "multi_minimize_float":
            metadata.get(fun.name, {}).get("multi_minimize_float", []) +
            [minimize_function],
        },
    )
    return fun, [minimize_function], metadata


def hide(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects more than zero arguments.

    It does not modify the original definition. It makes sure that no
    grammar nodes are generated from the var names passed as arguments.
    """
    assert len(args) != 0

    # TODO How can I verify if the function is in the context?
    def get_var_name(arg):
        if isinstance(arg, SVar):
            return arg.name
        else:
            raise_decorator_error("hide")

    # rethink this
    aux_dict = {"hide": [get_var_name(arg) for arg in args]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def hide_types(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects more than zero arguments.

    It does not modify the original definition. It makes sure that no
    grammar nodes are generated from the var names passed as arguments.
    """
    assert len(args) != 0

    # TODO How can I verify if the function is in the context?
    def get_var_name(arg):
        if isinstance(arg, SVar):
            return arg.name
        else:
            raise_decorator_error("hide_types")

    # rethink this
    aux_dict = {"hide_types": [get_var_name(arg) for arg in args]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def error_fitness(
        args: list[STerm], fun: Definition,
        metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects one argument .

    It does not modify the original definition. It makes sure that
    the error fitness in case of any exception during the synthesis is the one defined in the argument
    """
    assert len(args) == 1

    aux_dict = {"error_fitness": args[0]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def objective_number(
        args: list[STerm], fun: Definition,
        metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects one argument .
    It does not modify the original definition. It specifies the number of objective for multi objective problems
    """
    assert len(args) == 1

    aux_dict = {"objective_number": args[0]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def disable_control_flow(
        args: list[STerm], fun: Definition,
        metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects zero arguments .

    It does not modify the original definition. It makes sure that
    the control flow grammar nodes are allowed during synthesis
    """
    assert len(args) == 0

    aux_dict = {"disable_control_flow": True}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def allow_recursion(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a zero argument .

    It does not modify the original definition. It makes sure that
    recursion can be used during synthesis
    """
    assert len(args) == 0

    aux_dict = {"recursion": True}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata
