from aeon.decorators import decorators_environment
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import BaseType
from aeon.core.types import Type
from aeon.sugar.program import Definition
from aeon.sugar.program import Decorator

single_objective_decorators = ["minimize", "maximize", "assert_property"]
multi_objective_decorators = [
    "multi_minimize",
    "multi_maximize",
    "assert_properties",
]


def get_minimize(minimize: list[bool]):
    if len(minimize) == 1:
        return minimize[0]
    else:
        return minimize


def get_type_from_decorators(macro_list) -> BaseType:
    if len(macro_list) == 1:
        if macro_list[0].name in single_objective_decorators:
            return BaseType("Float")
        elif macro_list[0].name in multi_objective_decorators:
            return BaseType("List")
        else:
            raise Exception(
                "decorator not in lists single and multi objective decorators",
            )
    else:
        raise NotImplementedError("Not yet supported")


def extract_fitness_from_synth(d: Definition) -> tuple[Term, list[Decorator]]:
    decorators_list: list[Decorator] = d.decorators
    assert len(decorators_list) > 0

    fitness_terms: list[Term] = []
    for dec in decorators_list:
        annotation_func = getattr(decorators_environment, dec.name)
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
    fitness_args: list[tuple[str, Type]],
    fitness_return_type: BaseType,
    fitness_terms: list[Term],
) -> Definition:
    if len(fitness_terms) == 1:
        return Definition(
            name="fitness",
            args=[],
            type=fitness_return_type,
            body=fitness_terms[0],
        )
    else:
        raise NotImplementedError("Not yet supported")


def generate_term(
    fitness_name: str,
    fitness_return_type: BaseType,
    fitness_terms: list[Term],
) -> Term:
    if len(fitness_terms) == 1:
        rec_name = f"fitness_{fitness_name}"
        return Rec(
            var_name=rec_name,
            var_type=fitness_return_type,
            var_value=fitness_terms[0],
            body=Var(rec_name),
        )
    else:
        raise NotImplementedError("Not yet supported")
