from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import Optional

from geneticengine.core.decorators import abstract
from geneticengine.core.grammar import extract_grammar
from lark.lexer import Token

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
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import synth

prelude_ops = ["%", "/", "*", "-", "+", ">=", ">", "<=", "<", "!=", "==", "print", "native_import", "native"]

aeon_to_python_types = {"Int": int, "Bool": bool, "String": str, "Float": float}

# Probably move this methoad to another file
def refined_to_unrefinedtype(ty: RefinedType) -> Type:
    return ty.type


def find_class_by_name(class_name: str, grammar_nodes: list(type)) -> tuple[list(type), type]:
    """This function iterates over the provided list of grammar nodes and
    returns the node whose name matches the provided name. If no match is found
    it creates a new abstract class and a new data class, adds them to the
    list, and returns the abstract class and the updated list of grammar nodes.

    Args:
        class_name (str): The name of the class to find.
        grammar_nodes (list[type]): A list of grammar nodes to search through.

    Returns:
        tuple[list[type], type]: A tuple containing the updated list of grammar nodes and the found or newly created class.
    """
    for cls in grammar_nodes:
        if cls.__name__ in [class_name, "t_" + class_name]:
            return grammar_nodes, cls
    if class_name in list(aeon_to_python_types.keys()):
        new_abs_class = type("t_" + class_name, (ABC,), {})
        # new_abs_class = type("t_"+class_name, (), {})
        # new_abs_class = abstract(new_abs_class)
        grammar_nodes.append(new_abs_class)

        new_class = dataclass(
            type(
                "literal_" + class_name,
                (new_abs_class,),
                {"__annotations__": {"value": aeon_to_python_types[class_name]}},
            ),
        )
        grammar_nodes.append(new_class)

    else:
        new_abs_class = type(class_name, (ABC,), {})
        grammar_nodes.append(new_abs_class)
    return grammar_nodes, new_abs_class


def get_fitness_term(term: Rec) -> Term:
    if term.var_name == "fitness":
        return term.var_value
    elif isinstance(term.body, Rec):
        return get_fitness_term(term.body)
    else:
        raise NotImplementedError("Fitness function not found")


def extract_fitness(term: Term):
    assert isinstance(term, Rec)
    fitness_term = get_fitness_term(term)
    print("fitness_body:", fitness_term)


# dict (hole_name , (hole_type, hole_typingContext))
def get_holes_type(
    ctx: TypingContext,
    t: Term,
    ty: Type,
    holes: dict(str, tuple(Type | None, TypingContext)) = None,
) -> dict(str, tuple(Type | None, TypingContext)):
    """Retrieve the Types of "holes" in a given Term and TypingContext.

    This function recursively navigates through the Term 't', updating the TypingContext and hole Type as necessary.
    When a hole is found, its Type and the current TypingContext are added to a dictionary, with the hole name as key.

    Args:
        ctx (TypingContext): The current TypingContext.
        t (Term): The term to analyze.
        ty (Type): The current type.
        holes (dict[str, tuple[Type | None, TypingContext]]): The current dictionary of hole types. Defaults to None.

    Returns:
        dict[str, tuple[Type | None, TypingContext]]: The updated dictionary of hole Types and their TypingContexts.
    """

    if holes is None:
        holes = {}

    if isinstance(t, Rec):
        ctx = ctx.with_var(t.var_name, t.var_type)
        holes = get_holes_type(ctx, t.var_value, t.var_type, holes)
        holes = get_holes_type(ctx, t.body, ty, holes)

    elif isinstance(t, Let):
        _, t1 = synth(ctx, t.var_value)
        ctx = ctx.with_var(t.var_name, t1)
        holes = get_holes_type(ctx, t.var_value, ty, holes)
        holes = get_holes_type(ctx, t.body, ty, holes)

    elif isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        ret = substitution_in_type(ty.type, Var(t.var_name), ty.var_name)
        ctx = ctx.with_var(t.var_name, ty.var_type)

        holes = get_holes_type(ctx, t.body, ret, holes)

    elif isinstance(t, If):
        holes = get_holes_type(ctx, t.then, ty, holes)
        holes = get_holes_type(ctx, t.otherwise, ty, holes)

    elif isinstance(t, Application):
        holes = get_holes_type(ctx, t.fun, ty, holes)
        holes = get_holes_type(ctx, t.arg, ty, holes)

    elif isinstance(t, Annotation) and isinstance(t.expr, Hole):
        holes[t.expr.name] = (t.type, ctx)

    elif isinstance(t, Hole):
        ty = refined_to_unrefinedtype(ty) if isinstance(ty, RefinedType) else ty
        holes[t.name] = (ty, ctx)

    return holes


def gen_class_attr_and_superclass(class_type: Type, grammar_nodes: list(type)) -> tuple(dict(str, type), type):
    """Generates the attributes and superclass from a Type object.

    This function takes a object type and a list of grammar nodes. It iterates over the Type object as long as
    it is an instance of AbstractionType. For each iteration, it retrieves an attribute name and type,
    and adds them to the fields dictionary. After the loop, it returns the fields and a superclass.

    Args:
        class_type (type): The class type to generate attributes and superclass for.
        grammar_nodes (list[type]): The list of grammar nodes to search for classes.

    Returns:
        tuple(dict(str, type), type): A tuple containing the fields dictionary and the superclass.
    """
    fields = {}
    while isinstance(class_type, AbstractionType):
        attribute_name = class_type.var_name.value if isinstance(class_type.var_name, Token) else class_type.var_name

        attribute_type = (
            refined_to_unrefinedtype(class_type.var_type)
            if isinstance(class_type.var_type, RefinedType)
            else class_type.var_type
        )

        grammar_nodes, cls = find_class_by_name(attribute_type.name, grammar_nodes)

        fields[attribute_name] = cls

        class_type = class_type.type
    return fields, class_type


def create_class_fromm_ctx_var(var: tuple, grammar_nodes: list(type)) -> list(type):
    """Creates a new class based on a context variable and adds it to the list
    of grammar nodes.

    This function takes a context variable (a tuple with the class name and type) and a list of existing grammar nodes.
    It creates a new class with the given name, and generate his attributes and superclass based on the type provided by the tuple.
    The new class is then added to the list of grammar nodes. If the class name is in the prelude operations or starts with "_anf_",
    no class is created and the original list of grammar nodes is returned.

    Args:
        var (tuple): A tuple containing the class name and type.
        grammar_nodes (list[type]): The list of existing grammar nodes.

    Returns:
        list[type]: The updated list of grammar nodes with the new class added, or the original list if no class was added.
    """
    class_name = var[0].value if isinstance(var[0], Token) else var[0]
    class_type = var[1]

    if class_name not in prelude_ops and not class_name.startswith("_anf_"):

        fields, parent_type = gen_class_attr_and_superclass(class_type, grammar_nodes)

        # TODO handle type top and bottom
        if isinstance(parent_type, (Top, Bottom)):
            return grammar_nodes

        parent_class_name = parent_type.name
        grammar_nodes, parent_class = find_class_by_name(parent_class_name, grammar_nodes)

        new_class = type("app_" + class_name, (parent_class,), {"__annotations__": dict(fields)})

        # print(">>", new_class.__name__, "\n", new_class.__annotations__, "\n")

        grammar_nodes.append(new_class)

    return grammar_nodes


def gen_grammar_nodes(ctx: TypingContext, grammar_nodes: list[type] = []) -> list[type]:
    """Generate grammar nodes from the variables in the given TypingContext.

    This function iterates over the variables in the provided TypingContext. For each variable,
    it generates a new class using the create_class_from_ctx_var function and adds it to
    the list of grammar_nodes. If no initial list of grammar_nodes is provided, it starts with an empty list.

    Args:
        ctx (TypingContext): The TypingContext to extract variables from.
        grammar_nodes (list[type]): Initial list of grammar nodes. Defaults to an empty list.

    Returns:
        list[type]: The list of generated grammar nodes.
    """
    for var in ctx.vars():
        grammar_nodes = create_class_fromm_ctx_var(var, grammar_nodes)
        if isinstance(var[1], AbstractionType):
            # grammar_nodes = create_super_class
            pass
    return grammar_nodes


def get_grammar_node(node_name: str, nodes: list[type]) -> type:
    """Returns the node from the provided list of nodes whose name matches the
    provided name. If no match is found, the function returns None.

    Args:
        node_name (str): The name of the node to retrieve.
        nodes (list[type]): A list of nodes to search through.

    Returns:
        type: The node with the matching name
    """
    return (n for n in nodes if n.__name__ == node_name)


def synthesis(ctx: TypingContext, p: Term, ty: Type):
    print("###\n", ctx)

    holes = get_holes_type(ctx, p, ty)

    first_hole = next(iter(holes))
    hole_type, hole_ctx = holes[first_hole]

    print(hole_ctx, ":", type(hole_ctx))

    grammar_n = gen_grammar_nodes(hole_ctx)

    for cls in grammar_n:
        print(cls, "\nattributes: ", cls.__annotations__, "\nparent class: ", cls.__bases__, "\n")

    # starting_node = get_grammar_node(hole_type.name, grammar_n)

    # extract_fitness(p)
    # grammar = extract_grammar(grammar_nodes, starting_node)
    # print(grammar)
