from __future__ import annotations

import sys

from geneticengine.core.grammar import extract_grammar

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.synthesis_grammar.grammar import build_grammar_core
from aeon.synthesis_grammar.grammar import build_grammar_sugar
from aeon.synthesis_grammar.grammar import find_class_by_name
from aeon.synthesis_grammar.grammar import get_holes_type
from aeon.typechecking.typeinfer import check_type_errors
from aeon.utils.ctx_helpers import build_context

if __name__ == "__main__":
    fname = sys.argv[1]
    with open(fname) as f:
        code = f.read()

    if "--core" in sys.argv:
        ctx = build_context(typing_vars)
        ectx = EvaluationContext(evaluation_vars)
        p = parse_term(code)
        print("##\n", ctx)
    else:
        prog: Program = parse_program(code)
        p, ctx, ectx = desugar(prog)
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
        print("###\n", ctx)
        holes = {}
        holes = get_holes_type(p, top, ctx)
        for key, value in holes.items():
            print(key, " : ", value, "\n")

        # TODO  extract the nodes from p instead of defs and type_decl
        grammar_n: list[type] = build_grammar_core(p)
        for cls in grammar_n:
            print(cls, "\nattributes: ", cls.__annotations__, "\nparent class: ", cls.__bases__, "\n")

        first_hole = next(iter(holes))
        hole_ctx = holes[first_hole][1]

        fitness_function = extract_fitness(p, hole_ctx)

        # grammar = extract_grammar(grammar_nodes, starting_node)

        eval(p, ectx)
