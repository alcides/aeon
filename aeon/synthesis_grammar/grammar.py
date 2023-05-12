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


# Probably move this methoad to another file
def refined_to_unrefinedtype(ty: RefinedType) -> Type:
    return ty.type


def find_class_by_name(grammar_nodes: list(type), class_name: str) -> tuple[list(type), type]:
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

        grammar_nodes, cls = find_class_by_name(grammar_nodes, term_var_type.name)

        var_name = t.var_name.value if isinstance(t.var_name, Token) else t.var_name

        fields[var_name] = cls
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


def extract_fitness(term: Term, ctx: TypingContext):
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


def synthesis(ctx: TypingContext, p: Term, ty: Type):
    print("###\n", ctx)

    holes = get_holes_type(ctx, p, ty)
    for key, value in holes.items():
        print(key, " : ", value, "\n")

    grammar_n: list[type] = build_grammar_core(p)
    for cls in grammar_n:
        print(cls, "\nattributes: ", cls.__annotations__, "\nparent class: ", cls.__bases__, "\n")

    first_hole = next(iter(holes))
    hole_ctx = holes[first_hole][1]

    extract_fitness(p, hole_ctx)

    # grammar = extract_grammar(grammar_n, starting_node)
    # print(grammar)
