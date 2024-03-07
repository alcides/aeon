"""A decorator represents the modification of the program around a function.
Consider the following example:

@decorator_name(decorator_arg, decorator_arg2)
def fun(...) { ... }

The decorator implementation will receive the list [decorator_arg, decorator_arg2] and the definition of fun.
Then the implementation should return a tuple of the (possibly modified) definition, as well as a list of
eventual complementary definitions.
"""

from aeon.core.terms import Var
from aeon.core.types import BaseType
from aeon.decorators.api import DecoratorType
from aeon.decorators.api import Metadata
from aeon.sugar.program import Definition
from aeon.synthesis_grammar.decorators import minimize_int, minimize_float, multi_minimize_float, syn_ignore
from aeon.synthesis_grammar.utils import fitness_function_name_for

decorators_environment: dict[str, DecoratorType] = {
    "minimize_int": minimize_int,
    "minimize_float": minimize_float,
    "multi_minimize_float": multi_minimize_float,
    "syn_ignore": syn_ignore,
}

fitness_decorators = ["minimize_int", "minimize_float", "multi_minimize_float"]


# Is this the right place for the method?
def create_fitness_function(fun_name: str, total_extra: list[Definition], metadata: Metadata) -> list[Definition]:
    """
    Creates a fitness function for the specified function name based on decorators used.
    The fitness function aggregates objectives from used decorators into a single or multiple objective(s).
    """
    if fun_name not in metadata:
        return total_extra
    used_decorators = [x for x in fitness_decorators if x in metadata[fun_name].keys()]
    if used_decorators:
        objectives_list: list[Definition] = [
            objective for decorator in used_decorators for objective in metadata[fun_name][decorator]
        ]

        if len(objectives_list) > 1:
            fitness_base_type = BaseType("List")
            fitness_body = None  # TODO

        else:
            fitness_base_type = objectives_list[0].type  # type: ignore
            fitness_body = Var(objectives_list[0].name)

        fitness_function = Definition(
            name=fitness_function_name_for(fun_name),
            args=[],
            type=fitness_base_type,
            body=fitness_body,
        )
        total_extra.append(fitness_function)
    return total_extra


def apply_decorators(fun: Definition, metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    "Applies each decorator in order, and returns the cumulative list of possible new definitions."
    if not metadata:
        metadata = {}
    total_extra = []
    for decorator in fun.decorators:
        if decorator.name not in decorators_environment:
            raise Exception(f"Unknown decorator named {decorator.name}, in function {fun.name}.")
        decorator_processor = decorators_environment[decorator.name]
        (fun, extra, metadata) = decorator_processor(decorator.macro_args, fun, metadata)
        total_extra.extend(extra)
    total_extra = create_fitness_function(fun.name, total_extra, metadata)
    # criar aqui a fitness function
    return fun, total_extra, metadata
