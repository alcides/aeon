from __future__ import annotations

import sys
from abc import ABC
from typing import Union
from Levenshtein import distance
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors
from aeon.core.types import Bottom
from aeon.core.types import Top

from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.grammar import extract_grammar

from aeon.core.types import AbstractionType
from aeon.sugar.program import Definition
from aeon.sugar.program import TypeDecl
from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.program import Program
from aeon.sugar.parser import parse_program
from aeon.utils.ctx_helpers import build_context
from geneticengine.core.problems import SingleObjectiveProblem

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
        _, typ = find_class_by_name(
            grammar_nodes, t.var_type.name)
        fields[t.var_name] = typ
        t = t.type
        
    # TODO handle type top and bottom
    if isinstance(t, (Top, Bottom)):
        return grammar_nodes

    parent_class_name = t.name

    grammar_nodes, parent_class = find_class_by_name(
        grammar_nodes, parent_class_name)

    new_class_dict = {
        '__annotations__': dict(fields)
    }
    new_class = type(definition.name, (parent_class, ), new_class_dict)

    #print(new_class.__name__, "\n", new_class.__annotations__, "\n")

    def str_method(self):
        # wrong representation
        field_values = [
            f'("{str(getattr(self, field_name))}")' for field_name, _ in definition.args]
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
        grammar_nodes, typ = find_class_by_name(
            grammar_nodes, t.var_type.name)
        fields[t.var_name] = typ
        t = t.type

    # TODO handle type top and bootom
    if isinstance(t, (Top, Bottom)):
        return grammar_nodes

    parent_class_name = t.name

    grammar_nodes, parent_class = find_class_by_name(
        grammar_nodes, parent_class_name)

    new_class_dict = {
        '__annotations__': dict(fields)
    }
    new_class = type(term.var_name, (parent_class, ), new_class_dict)

    #print(new_class.__name__, "\n", new_class.__annotations__, "\n")
    # TODO
    def str_method(self):
        return f" "

    new_class.__str__ = str_method
    grammar_nodes.append(new_class)

    return grammar_nodes


def build_grammar_core(term: Term, grammar_nodes: list[type]) -> list[type]:
    rec = term
    while isinstance(rec, Rec):
        grammar_nodes = create_class_from_rec_term(rec, grammar_nodes)
        rec = rec.body
    return grammar_nodes

# fitness function just to test grammar from sugar


def fitness_function(individual):
    guess = str(individual)
    target = "Image_draw_rectangle(Image_draw_rectangle(Image_draw_rectangle(Image_draw_rectangle(Image_draw_rectangle(canvas)(rect1_coord)(key_color))(rect2_coord)(white_color))(rect3_coord)(key_color))(rect4_coord)(key_color))(rect5_coord)(key_color)"
    lev_distance = distance(guess, target)
    return 1 / (lev_distance + 1)


def test_geneticengine(g):
    alg = SimpleGP(
        g,
        problem=SingleObjectiveProblem(
            minimize=True,
            fitness_function=fitness_function,
        ),
        max_depth=10,
        number_of_generations=100,
        population_size=500,
    )
    best = alg.evolve()
    return best

# TODO
def get_holes_type(prog: Term) -> dict(str, tuple(Union[Type, None], TypingContext)):
    holes = {}
    return


if __name__ == "__main__":
    fname = sys.argv[1]
    with open(fname) as f:
        code = f.read()

    if "--core" in sys.argv:
        ctx = build_context(typing_vars)
        ectx = EvaluationContext(evaluation_vars)
        p = parse_term(code)
    else:
        prog: Program = parse_program(code)
        p, ctx, ectx, defs, type_decls = desugar(prog)
    if "-d" in sys.argv or "--debug" in sys.argv:
        print(p)

    errors = check_type_errors(ctx, p, top)
    if errors:
        print("-------------------------------")
        print("+  Type Checking Error        +")
        for error in errors:
            print("-------------------------------")
            print(error)

        print("-------------------------------")

    else:

        # TODO  extract the nodes from p instead of defs and type_decls
        holes = {}
        holes = get_holes_type(p)
        grammar_n: list[type] = build_grammar_core(p, [])

        for cls in grammar_n:
            print(cls)
        print(len(grammar_n))
        print("##############")

        # grammar from sugar
        synth_funcs = ([d for d in prog.definitions
                        if d.name.startswith("synth_")])

        grammar_nodes: list[type] = build_grammar_sugar(defs, type_decls)
        for cls in grammar_nodes:
            print(cls)
        print(len(grammar_nodes))

        _, starting_node = find_class_by_name(
            grammar_nodes, synth_funcs[0].body.var_value.type.name)

        grammar = extract_grammar(grammar_nodes, starting_node)

        eval(p, ectx)
