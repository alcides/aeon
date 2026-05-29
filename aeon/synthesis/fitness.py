from aeon.decorators import decorators_environment
from aeon.sugar.program import Definition, SLiteral, SRec, STerm, SVar
from aeon.sugar.program import Decorator
from aeon.sugar.stypes import SType
from aeon.sugar.ast_helpers import st_float
from aeon.synthesis.decorators import multi_objective_type
from aeon.utils.name import Name, fresh_counter

single_objective_decorators = ["minimize", "maximize", "assert_property"]
multi_objective_decorators = [
    "multi_minimize",
    "multi_maximize",
    "multi_minimize_float",
    "multi_minimize_int",
    "assert_properties",
]


def get_minimize(minimize: list[bool]):
    if len(minimize) == 1:
        return minimize[0]
    else:
        return minimize


def _objective_count(decorator: Decorator) -> int:
    """Number of objectives a multi-objective decorator declares.

    Multi-objective decorators take the objective count as a trailing integer
    literal argument (e.g. ``@multi_minimize_float(errors synth, 3)``); fall
    back to a single objective when none is provided.
    """
    for arg in reversed(getattr(decorator, "macro_args", []) or []):
        if isinstance(arg, SLiteral) and isinstance(arg.value, int):
            return arg.value
    return 1


def get_type_from_decorators(macro_list) -> SType:
    if len(macro_list) == 1:
        decorator = macro_list[0]
        decorator_name = decorator.name.name if isinstance(decorator.name, Name) else str(decorator.name)
        if decorator_name in single_objective_decorators:
            return st_float
        elif decorator_name in multi_objective_decorators:
            # Multi-objective fitness is the language's native ``Array`` type,
            # refined so its length equals the number of objectives (one element
            # per objective). See issue #294.
            return multi_objective_type("Float", _objective_count(decorator))
        else:
            raise Exception(
                "decorator not in lists single and multi objective decorators",
            )
    else:
        raise NotImplementedError("Not yet supported")


def extract_fitness_from_synth(d: Definition) -> tuple[STerm, list[Decorator]]:
    decorators_list: list[Decorator] = d.decorators
    assert len(decorators_list) > 0

    fitness_terms: list[STerm] = []
    for dec in decorators_list:
        annotation_func = getattr(decorators_environment, str(dec.name))
        expr_term = annotation_func(dec.macro_args)
        add_to_list(expr_term, fitness_terms)

    assert len(fitness_terms) > 0

    fitness_return_type = get_type_from_decorators(decorators_list)

    fitness_function = generate_term(
        d.name,
        fitness_return_type,
        fitness_terms,
    )

    return fitness_function, decorators_list


def add_to_list(item: list, my_list: list):
    try:
        my_list += item if isinstance(item, list) else [item]
    except TypeError as e:
        raise TypeError(f"An error occurred while adding to the list: {e}")

    return my_list


def generate_definition(
    fitness_args: list[tuple[str, SType]],
    fitness_return_type: SType,
    fitness_terms: list[STerm],
) -> Definition:
    if len(fitness_terms) == 1:
        return Definition(
            name=Name("fitness", fresh_counter.fresh()),
            foralls=[],
            args=[],
            type=fitness_return_type,
            body=fitness_terms[0],
        )
    else:
        raise NotImplementedError("Not yet supported")


def generate_term(
    fitness_name: Name,
    fitness_return_type: SType,
    fitness_terms: list[STerm],
) -> STerm:
    if len(fitness_terms) == 1:
        rec_name = Name(f"fitness_{fitness_name}", fresh_counter.fresh())
        return SRec(
            var_name=rec_name,
            var_type=fitness_return_type,
            var_value=fitness_terms[0],
            body=SVar(rec_name),
            decreasing_by=(),
        )
    else:
        raise NotImplementedError("Not yet supported")
