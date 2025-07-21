"""Meta-programming code for optimization-related decorators."""

from typing import NamedTuple
from aeon.decorators.api import Metadata, metadata_update
from aeon.sugar.program import Definition, STerm, SVar
from aeon.sugar.stypes import STypeConstructor
from aeon.sugar.ast_helpers import st_int, st_float
from aeon.utils.name import Name, fresh_counter

from aeon.sugar.program import SLiteral


def raise_decorator_error(name: str) -> None:
    raise Exception(f"Exception in decorator named {name}.")


class Goal(NamedTuple):
    minimize: bool
    length: int
    function: Name


def make_optimizer(
    args: list[STerm], fun: Definition, metadata: Metadata, typ: STypeConstructor, minimize: bool, length: int = 1
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition).

    It does not modify the original definition, but appends a new
    definition to the program. This new definition has the name
    "_fitness_function", prefixed by the original definition's name
    """
    current_goals = metadata.get(fun.name, {}).get("goals", [])
    minimize_name = "minimize" if minimize else "maximize"
    function_name = Name(f"__internal__{minimize_name}_{type}_{fun.name}_{len(current_goals)}", fresh_counter.fresh())
    function = Definition(
        name=function_name,
        foralls=[],
        args=[],
        type=typ,
        body=args[0],
    )
    goal = Goal(minimize, length, function_name)

    metadata = metadata_update(
        metadata,
        fun,
        {
            "goals": current_goals + [goal],
        },
    )
    return fun, [function], metadata


def minimize_int(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(args) == 1, "minimize_int decorator expects a single argument"
    return make_optimizer(args, fun, metadata, st_int, minimize=True)


def minimize_float(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(args) == 1, "minimize_float decorator expects a single argument"
    return make_optimizer(args, fun, metadata, st_float, minimize=True)


def multi_minimize_float(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects a single argument (the body of the definition)."""
    assert (
        len(
            args,
        )
        == 1
    ), "multi_minimize_float decorator expects a single argument"
    assert isinstance(args[1], SLiteral)
    assert isinstance(args[1].value, int), "multi_minimize_float decorator expects an integer argument"
    number_of_objectives = args[1].value
    return make_optimizer(
        args, fun, metadata, STypeConstructor(Name("List", 0)), minimize=True, length=number_of_objectives
    )


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
    args: list[STerm], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
    """This decorator expects one argument .

    It does not modify the original definition. It makes sure that
    the error fitness in case of any exception during the synthesis is the one defined in the argument
    """
    assert len(args) == 1

    aux_dict = {"error_fitness": args[0]}
    metadata = metadata_update(metadata, fun, aux_dict)

    return fun, [], metadata


def disable_control_flow(
    args: list[STerm], fun: Definition, metadata: Metadata
) -> tuple[Definition, list[Definition], Metadata]:
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
