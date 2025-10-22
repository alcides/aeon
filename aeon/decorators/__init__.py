"""A decorator represents the modification of the program around a function.
Consider the following example:

@decorator_name(decorator_arg, decorator_arg2)
def fun(...) { ... }

The decorator implementation will receive the list [decorator_arg, decorator_arg2] and the definition of fun.
Then the implementation should return a tuple of the (possibly modified) definition, as well as a list of
eventual complementary definitions.
"""

from aeon.decorators.api import DecoratorType
from aeon.decorators.api import Metadata
from aeon.sugar.program import Definition
from aeon.synthesis.decorators import (
    minimize_int,
    minimize_float,
    multi_minimize_float,
    hide,
    hide_types,
    allow_recursion,
    error_fitness,
    disable_control_flow,
    prompt,
)

decorators_environment: dict[str, DecoratorType] = {
    "minimize_int": minimize_int,
    "minimize_float": minimize_float,
    "multi_minimize_float": multi_minimize_float,
    "hide": hide,
    "hide_types": hide_types,
    "allow_recursion": allow_recursion,
    "error_fitness": error_fitness,
    "disable_control_flow": disable_control_flow,
    "prompt": prompt,
}


def apply_decorators(fun: Definition, metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    "Applies each decorator in order, and returns the cumulative list of possible new definitions."
    if not metadata:
        metadata = {}
    total_extra = []
    for decorator in fun.decorators:
        dname = decorator.name.name
        if dname not in decorators_environment:
            raise Exception(f"Unknown decorator named {dname}, in function {fun.name}.")
        decorator_processor = decorators_environment[dname]
        (fun, extra, metadata) = decorator_processor(decorator.macro_args, fun, metadata)
        total_extra.extend(extra)
    return fun, total_extra, metadata
