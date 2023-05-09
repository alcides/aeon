from __future__ import annotations

from abc import ABC
from typing import Any
from typing import Callable
from typing import Optional

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


def find_class_by_name(grammar_nodes: list(type), class_name: str) -> tuple[list(type), type]:
    for cls in grammar_nodes:
        if cls.__name__ == class_name:
            return grammar_nodes, cls
    new_class = type(class_name, (ABC,), {})
    grammar_nodes.append(new_class)
    return grammar_nodes, new_class


def create_dataclass_from_definition(definition: Definition, grammar_nodes: list(type)):
    fields = {arg_name: arg_type for arg_name, arg_type in definition.args}

    t = definition.type
    while isinstance(t, AbstractionType):
        # TODO replace basetype Int, Bool etc with <class 'int'>, <class 'bool'> etc
        # TODO handle refined type
        _, typ = find_class_by_name(grammar_nodes, t.var_type.name)
        fields[t.var_name] = typ
        t = t.type

    # TODO handle type top and bottom
    if isinstance(t, (Top, Bottom)):
        return grammar_nodes

    parent_class_name = t.name

    grammar_nodes, parent_class = find_class_by_name(grammar_nodes, parent_class_name)

    new_class_dict = {"__annotations__": dict(fields)}
    new_class = type(definition.name, (parent_class,), new_class_dict)

    # print(new_class.__name__, "\n", new_class.__annotations__, "\n")

    def str_method(self):
        # wrong representation
        field_values = [f'("{str(getattr(self, field_name))}")' for field_name, _ in fields]
        return f"{definition.name} {' '.join(field_values)}"

    new_class.__str__ = str_method
    grammar_nodes.append(new_class)

    return grammar_nodes


def build_grammar_sugar(defs: list[Definition], type_decls: list[TypeDecl]) -> list[type]:
    grammar_nodes: list[type] = []

    for ty in type_decls:
        if ty.name not in [cls.__name__ for cls in grammar_nodes]:
            type_dataclass = type(ty.name, (ABC,), {})
            grammar_nodes.append(type_dataclass)
    for d in defs:
        # TODO if it is uninterpreted do not create a dataclass ?
        # if (not isinstance(d.type, AbstractionType)):
        grammar_nodes = create_dataclass_from_definition(d, grammar_nodes)

    return grammar_nodes


def create_class_from_rec_term(term: Rec, grammar_nodes: list(type)):
    fields = {}
    t = term.var_type
    while isinstance(t, AbstractionType):
        # TODO replace basetype Int, Bool etc with <class 'int'>, <class 'bool'> etc
        # TODO handle refined type
        grammar_nodes, typ = find_class_by_name(grammar_nodes, t.var_type.name)

        var_name = t.var_name.value if isinstance(t.var_name, Token) else t.var_name

        fields[var_name] = typ
        t = t.type

    # TODO handle type top and bottom
    if isinstance(t, (Top, Bottom)):
        return grammar_nodes

    parent_class_name = t.name

    grammar_nodes, parent_class = find_class_by_name(grammar_nodes, parent_class_name)

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


# Probably change this methoad for another file
def refined_to_unrefinedtype(ty: RefinedType) -> Type:
    return ty.type


# dict (hole_name , (hole_type, hole_typingContext))
def get_holes_type(
    t: Term,
    ty: Type,
    ctx: TypingContext,
    holes: dict(str, tuple(Type | None, TypingContext)) = None,
) -> dict(str, tuple(Type | None, TypingContext)):

    if holes is None:
        holes = {}

    if isinstance(t, Rec):
        ctx = ctx.with_var(t.var_name, t.var_type)
        holes = get_holes_type(t.var_value, t.var_type, ctx, holes)
        holes = get_holes_type(t.body, ty, ctx, holes)

    elif isinstance(t, Let):
        # not sure If the use of synth is the best option to get the type
        _, t1 = synth(ctx, t.var_value)
        ctx = ctx.with_var(t.var_name, t1)
        holes = get_holes_type(t.var_value, ty, ctx, holes)
        holes = get_holes_type(t.body, ty, ctx, holes)

    elif isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        ret = substitution_in_type(ty.type, Var(t.var_name), ty.var_name)
        ctx = ctx.with_var(t.var_name, ty.var_type)

        holes = get_holes_type(t.body, ret, ctx, holes)

    elif isinstance(t, If):
        holes = get_holes_type(t.then, ty, ctx, holes)
        holes = get_holes_type(t.otherwise, ty, ctx, holes)

    elif isinstance(t, Application):
        holes = get_holes_type(t.fun, ty, ctx, holes)
        holes = get_holes_type(t.arg, ty, ctx, holes)

    elif isinstance(t, Annotation) and isinstance(t.expr, Hole):
        holes[t.expr.name] = (t.type, ctx)

    elif isinstance(t, Hole):
        ty = refined_to_unrefinedtype(ty) if isinstance(ty, RefinedType) else ty
        holes[t.name] = (ty, ctx)

    return holes
