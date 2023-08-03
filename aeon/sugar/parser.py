from __future__ import annotations

import pathlib

from lark import Lark

from aeon.core.substitutions import liquefy
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Maximize
from aeon.core.terms import Minimize
from aeon.core.terms import MultiObjectiveProblem
from aeon.core.types import AbstractionType
from aeon.core.types import RefinedType
from aeon.core.types import SoftRefinedType
from aeon.core.types import TypeVar
from aeon.frontend.parser import TreeToCore
from aeon.sugar.program import Definition
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl


class TreeToSugar(TreeToCore):
    def list(self, args):
        return args

    def program(self, args):
        return Program(args[0], args[1], args[2])

    def regular_imp(self, args):
        return ImportAe(args[0], [])

    def function_imp(self, args):
        return ImportAe(args[1], args[0])

    def type_decl(self, args):
        return TypeDecl(args[0])

    def def_cons(self, args):
        return Definition(args[0], [], args[1], args[2])

    def def_fun(self, args):
        return Definition(args[0], args[1], args[2], args[3])

    def empty_list(self, args):
        return []

    def args(self, args):
        return args

    def arg(self, args):
        return (args[0], args[1])

    def abstraction_et(self, args):
        return Annotation(
            Abstraction(args[0], args[2]),
            AbstractionType(args[0], args[1], TypeVar("?t")),
        )

    def soft_refined_t(self, args):
        hard_constraint = None
        soft_constraint = args[2]
        if len(args[2].children) > 1:
            hard_constraint = RefinedType(str(args[0]), args[1], liquefy(args[2].children[0]))
            soft_constraint = args[2].children[1]
        return SoftRefinedType(str(args[0]), args[1], hard_constraint, soft_constraint)

    def expression_min(self, args):
        return Minimize(args[0])

    def expression_max(self, args):
        return Maximize(args[0])

    def expression_multiobjective(self, args):
        return MultiObjectiveProblem(args[0], args[1])

    def expression_min_max(self, args):
        objective_list = [
            Minimize(arg.children[0]) if arg.data == "expression_min" else Maximize(arg.children[0]) for arg in args
        ]
        solution_list = [arg.children[0] for arg in args]

        return MultiObjectiveProblem(objective_list, solution_list)


def mk_parser(rule="start", start_counter=0):
    return Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_sugar.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        transformer=TreeToSugar(start_counter),
        import_paths=[pathlib.Path(__file__).parent.parent.absolute() / "frontend"],
    )


parse_program = mk_parser("program").parse
