from __future__ import annotations

import pathlib
from typing import Callable

from lark import Lark

from aeon.core.substitutions import liquefy
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.types import AbstractionType, RefinedType
from aeon.core.types import TypeVar
from aeon.frontend.parser import TreeToCore
from aeon.sugar.program import Definition, Polarity
from aeon.sugar.program import Decorator
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
        assert isinstance(args[1], list)
        return TypeDecl(args[0], args[1])

    def targs(self, args):
        return args

    def targ(self, args):
        return (args[0], args[1], Polarity.POSITIVE)

    def def_cons(self, args):
        if len(args) == 3:
            return Definition(args[0], [], args[1], args[2])
        else:
            decorators = args[0]
            return Definition(args[1], [], args[2], args[3], decorators)

    def def_fun(self, args):
        if len(args) == 4:
            return Definition(args[0], args[1], args[2], args[3])
        else:
            decorators = args[0]
            return Definition(args[1], args[2], args[3], args[4], decorators)

    def macros(self, args):
        return args

    def macro(self, args):
        return Decorator(args[0], args[1])

    def macro_args(self, args):
        return args

    def empty_list(self, args):
        return []

    def args(self, args):
        return args

    def arg(self, args):
        return (args[0], args[1])

    def refined_arg(self, args):
        return args[0], RefinedType(args[0], args[1], liquefy(args[2]))

    def abstraction_refined_t(self, args):
        type = RefinedType(args[0], args[1], liquefy(args[2]))
        return AbstractionType(str(args[0]), type, args[3])

    def abstraction_et(self, args):
        return Annotation(
            Abstraction(args[0], args[2]),
            AbstractionType(args[0], args[1], TypeVar("?t")),
        )


def mk_parser(rule="start", start_counter=0):
    return Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_sugar.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        transformer=TreeToSugar(start_counter),
        import_paths=[pathlib.Path(__file__).parent.parent.absolute() / "frontend"],
    )


parse_program: Callable[[str], Program] = mk_parser("program").parse
