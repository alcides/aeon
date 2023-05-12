from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import Any
from typing import Callable
from typing import Optional

from geneticengine.core.decorators import abstract
from geneticengine.core.grammar import extract_grammar
from lark.lexer import Token

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
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
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypeVar
from aeon.sugar.program import Definition
from aeon.sugar.program import TypeDecl
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import synth
from aeon.verification.horn import fresh

prelude_ops = ["%", "/", "*", "-", "+", ">=", ">", "<=", "<", "!=", "==", "print", "native_import", "native"]

# Probably move this methoad to another file
def refined_to_unrefinedtype(ty: RefinedType) -> Type:
    return ty.type


def find_class_by_name(class_name: str, grammar_nodes: list(type)) -> tuple[list(type), type]:
    for cls in grammar_nodes:
        if cls.__name__ in [class_name, "t_" + class_name]:
            return grammar_nodes, cls
    if class_name == "Int":
        new_abs_class = type("t_" + class_name, (ABC,), {})
        # new_abs_class = type("t_"+class_name, (), {})
        # new_abs_class = abstract(new_abs_class)
        grammar_nodes.append(new_abs_class)

        new_class = dataclass(type("literal_" + class_name, (new_abs_class,), {"__annotations__": {"value": int}}))
        grammar_nodes.append(new_class)

        return grammar_nodes, new_abs_class

    else:
        raise Exception("Not implemented: " + class_name)


def create_class_from_rec_term(term: Rec, grammar_nodes: list(type)) -> list(type):
    fields = {}
    t = term.var_type
    while isinstance(t, AbstractionType):
        term_var_type = refined_to_unrefinedtype(t.var_type) if isinstance(t.var_type, RefinedType) else t.var_type

        grammar_nodes, cls = find_class_by_name(term_var_type.name, grammar_nodes)

        var_name = t.var_name.value if isinstance(t.var_name, Token) else t.var_name

        fields[var_name] = cls
        t = t.type

    # TODO handle type top and bottom
    if isinstance(t, (Top, Bottom)):
        return grammar_nodes

    parent_class_name = t.name
    grammar_nodes, parent_class = find_class_by_name(parent_class_name, grammar_nodes)

    new_class_dict = {"__annotations__": dict(fields)}
    new_class = type(term.var_name, (parent_class,), new_class_dict)

    # print(new_class.__name__, "\n", new_class.__annotations__, "\n")
    def str_method(self):
        field_values = [f'("{str(getattr(self, field_name))}")' for field_name, _ in fields]
        return f"{term.name} {' '.join(field_values)}"

    new_class.__str__ = str_method
    grammar_nodes.append(new_class)

    return grammar_nodes


def build_grammar_core(term: Term, grammar_nodes: list[type] = []) -> list[type]:
    rec = term
    while isinstance(rec, Rec):
        grammar_nodes = create_class_from_rec_term(rec, grammar_nodes)
        rec = rec.body
    return grammar_nodes


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

    if holes is None:
        holes = {}

    if isinstance(t, Rec):
        ctx = ctx.with_var(t.var_name, t.var_type)
        holes = get_holes_type(ctx, t.var_value, t.var_type, holes)
        holes = get_holes_type(ctx, t.body, ty, holes)

    elif isinstance(t, Let):
        # not sure If the use of synth is the best option to get the type
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


def gen_class_attributes(class_type: type, grammar_nodes: list(type)):
    fields = {}
    while isinstance(class_type, AbstractionType):
        var_name = class_type.var_name.value if isinstance(class_type.var_name, Token) else class_type.var_name

        var_type = (
            refined_to_unrefinedtype(class_type.var_type)
            if isinstance(class_type.var_type, RefinedType)
            else class_type.var_type
        )

        grammar_nodes, cls = find_class_by_name(var_type.name, grammar_nodes)

        fields[var_name] = cls

        class_type = class_type.type
    return fields, class_type


def create_class_fromm_ctx_var(var: tuple, grammar_nodes: list(type)) -> list(type):
    class_name = var[0].value if isinstance(var[0], Token) else var[0]
    class_type = var[1]

    if class_name not in prelude_ops and not class_name.startswith("_anf_"):

        fields, parent_type = gen_class_attributes(class_type, grammar_nodes)

        # TODO handle type top and bottom
        if isinstance(parent_type, (Top, Bottom)):
            return grammar_nodes

        parent_class_name = parent_type.name
        grammar_nodes, parent_class = find_class_by_name(parent_class_name, grammar_nodes)

        new_class = type(class_name, (parent_class,), {"__annotations__": dict(fields)})

        # print(">>", new_class.__name__, "\n", new_class.__annotations__, "\n")

        grammar_nodes.append(new_class)

    return grammar_nodes


def gen_grammar_nodes(ctx: TypingContext, grammar_nodes: list[type] = []) -> list[type]:
    for var in ctx.vars():
        grammar_nodes = create_class_fromm_ctx_var(var, grammar_nodes)

    return grammar_nodes


def get_grammar_node(node_name: str, nodes: list[type]) -> type:
    return (n for n in nodes if n.__name__ == node_name)


def synthesis(ctx: TypingContext, p: Term, ty: Type):
    print("###\n", ctx)

    holes = get_holes_type(ctx, p, ty)

    first_hole = next(iter(holes))
    hole_type, hole_ctx = holes[first_hole]

    print(hole_ctx, ":", type(hole_ctx))

    # build grammar nodes from context of the hole

    grammar_n = gen_grammar_nodes(hole_ctx)

    for cls in grammar_n:
        print(cls, "\nattributes: ", cls.__annotations__, "\nparent class: ", cls.__bases__, "\n")

    # starting_node = get_grammar_node(hole_type.name, grammar_nodes)

    # extract_fitness(p)
    # grammar = extract_grammar(grammar_nodes, starting_node)
    # print(grammar)
