from typing import Union

from aeon.decorators import decorators_environment
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import refined_to_unrefined_type
from aeon.core.types import Type
from aeon.sugar.program import Definition
from aeon.sugar.program import Decorator
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import synth

singleObjectiveDecorators = ["minimize", "maximize", "assert_property"]
multiObjectiveDecorators = [
    "multi_minimize", "multi_maximize", "assert_properties"
]


# dict (hole_name , (hole_type, hole_typingContext, func_name))
def get_holes_info(
    ctx: TypingContext,
    t: Term,
    ty: Type,
    holes: Union[dict[str, tuple[Type, TypingContext, str]], None] = None,
    func_name: str = "",
) -> dict[str, tuple[Type, TypingContext, str]]:
    """Retrieve the Types of "holes" in a given Term and TypingContext.

    This function recursively navigates through the Term 't', updating the TypingContext and hole Type as necessary.
    When a hole is found, its Type and the current TypingContext are added to a dictionary, with the hole name as key.

    Args:
        ctx (TypingContext): The current TypingContext.
        t (Term): The term to analyze.
        ty (Type): The current type.
        holes (dict[str, tuple[Type, TypingContext, str]]: The current dictionary of hole types. Defaults to None.
        func_name (str) : The name of the function where the hole is defined.
    Returns:
        dict[str, tuple[Type, TypingContext, str]]: The updated dictionary of hole Types and their TypingContexts.
    """
    if holes is None:
        holes = {}
    if isinstance(t, Rec):
        if t.var_name.startswith("synth"):
            func_name = t.var_name

        ctx = ctx.with_var(t.var_name, t.var_type)
        holes = get_holes_info(
            ctx,
            t.var_value,
            t.var_type,
            holes,
            func_name,
        )
        holes = get_holes_info(ctx, t.body, ty, holes, func_name)

    elif isinstance(t, Let):
        _, t1 = synth(ctx, t.var_value)
        ctx = ctx.with_var(t.var_name, t1)
        holes = get_holes_info(ctx, t.var_value, ty, holes, func_name)
        holes = get_holes_info(ctx, t.body, ty, holes, func_name)

    elif isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        ret = substitution_in_type(ty.type, Var(t.var_name), ty.var_name)
        ctx = ctx.with_var(t.var_name, ty.var_type)
        holes = get_holes_info(ctx, t.body, ret, holes, func_name)

    elif isinstance(t, If):
        holes = get_holes_info(ctx, t.then, ty, holes, func_name)
        holes = get_holes_info(ctx, t.otherwise, ty, holes, func_name)

    elif isinstance(t, Application):
        holes = get_holes_info(ctx, t.fun, ty, holes, func_name)
        holes = get_holes_info(ctx, t.arg, ty, holes, func_name)

    elif isinstance(t, Annotation) and isinstance(t.expr, Hole):
        synth_func_name = func_name
        ty = refined_to_unrefined_type(t.type)
        holes[t.expr.name] = (ty, ctx, synth_func_name)

    elif isinstance(t, Hole):
        ty = refined_to_unrefined_type(ty)
        holes[t.name] = (ty, ctx, func_name)

    return holes


def get_minimize(minimize: list[bool]):
    if len(minimize) == 1:
        return minimize[0]
    else:
        return minimize


def get_type_from_decorators(macro_list) -> BaseType:
    if len(macro_list) == 1:
        if macro_list[0].name in singleObjectiveDecorators:
            return BaseType("Float")
        elif macro_list[0].name in multiObjectiveDecorators:
            return BaseType("List")
        else:
            raise Exception(
                "decorator not in lists single and multi objective decorators")
    else:
        raise Exception("Not yet supported")


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

    fitness_function = generate_term(d.name, fitness_return_type,
                                     fitness_terms)

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
        return Definition(name="fitness",
                          args=[],
                          type=fitness_return_type,
                          body=fitness_terms[0])
    else:
        raise Exception("Not yet supported")


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
        raise Exception("Not yet supported")
