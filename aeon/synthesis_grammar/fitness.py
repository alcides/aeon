from aeon.aeon_annotations import aeon_annotations
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
from aeon.sugar.program import Macro
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import synth


# dict (hole_name , (hole_type, hole_typingContext, func_name))
def get_holes_info_and_fitness_type(
    ctx: TypingContext,
    t: Term,
    ty: Type,
    holes: dict[str, tuple[Type, TypingContext, str]] | None = None,
    func_name: str = "",
    fitness_type: BaseType | None = None,
) -> tuple[dict[str, tuple[Type, TypingContext, str]], BaseType]:
    """Retrieve the Types of "holes" in a given Term and TypingContext.

    This function recursively navigates through the Term 't', updating the TypingContext and hole Type as necessary.
    When a hole is found, its Type and the current TypingContext are added to a dictionary, with the hole name as key.

    Args:
        ctx (TypingContext): The current TypingContext.
        t (Term): The term to analyze.
        ty (Type): The current type.
        holes (dict[str, tuple[Type, TypingContext, str]]: The current dictionary of hole types. Defaults to None.
        func_name (str) : The name of the function where the hole is defined.
        fitness_type (BaseType) : The type of the fitness function
    Returns:
        tuple[dict[str, tuple[Type, TypingContext, str]], BaseType]: The updated dictionary of hole Types and their TypingContexts.
    """
    if holes is None:
        holes = {}
    if isinstance(t, Rec):
        if t.var_name.startswith("synth"):
            func_name = t.var_name

        if t.var_name == "fitness":
            assert isinstance(t.var_type, BaseType), f"t.vartype = {type(t.var_type)}"
            fitness_type = t.var_type

        ctx = ctx.with_var(t.var_name, t.var_type)
        holes, fitness_type = get_holes_info_and_fitness_type(
            ctx,
            t.var_value,
            t.var_type,
            holes,
            func_name,
            fitness_type,
        )
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, t.body, ty, holes, func_name, fitness_type)

    elif isinstance(t, Let):
        _, t1 = synth(ctx, t.var_value)
        ctx = ctx.with_var(t.var_name, t1)
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, t.var_value, ty, holes, func_name, fitness_type)
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, t.body, ty, holes, func_name, fitness_type)

    elif isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        ret = substitution_in_type(ty.type, Var(t.var_name), ty.var_name)
        ctx = ctx.with_var(t.var_name, ty.var_type)
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, t.body, ret, holes, func_name, fitness_type)

    elif isinstance(t, If):
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, t.then, ty, holes, func_name, fitness_type)
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, t.otherwise, ty, holes, func_name, fitness_type)

    elif isinstance(t, Application):
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, t.fun, ty, holes, func_name, fitness_type)
        holes, fitness_type = get_holes_info_and_fitness_type(ctx, t.arg, ty, holes, func_name, fitness_type)

    elif isinstance(t, Annotation) and isinstance(t.expr, Hole):
        synth_func_name = func_name
        ty = refined_to_unrefined_type(t.type)
        holes[t.expr.name] = (ty, ctx, synth_func_name)

    elif isinstance(t, Hole):
        ty = refined_to_unrefined_type(ty)
        holes[t.name] = (ty, ctx, func_name)

    if not fitness_type:
        raise Exception("Fitness type is None")

    return holes, fitness_type


def get_minimize(minimize: list[bool]):
    if len(minimize) == 1:
        return minimize[0]
    else:
        return minimize


def extract_fitness_from_synth(d: Definition) -> tuple[Definition, list[bool]]:
    fitness_args: list[tuple[str, Type]] = d.args
    macro_list: list[Macro] = d.macros

    minimize_list: list[bool] = []
    fitness_terms: list[Term] = []
    for macro in macro_list:
        annotation_func = getattr(aeon_annotations, macro.name)
        expr_term, minimize = annotation_func(macro.macro_args)

        if minimize is not None:
            add_to_list(minimize, minimize_list)
        add_to_list(expr_term, fitness_terms)

    assert len(minimize_list) > 0
    assert len(fitness_terms) > 0

    fitness_return_type = BaseType("Float") if len(minimize_list) == 1 else BaseType("List")

    fitness_function = generate_definition(fitness_args, fitness_return_type, fitness_terms)

    return fitness_function, minimize_list


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
        return Definition(name="fitness", args=[], type=fitness_return_type, body=fitness_terms[0])
    else:
        raise Exception("Not yet supported")
