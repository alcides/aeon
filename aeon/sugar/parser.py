from __future__ import annotations

import pathlib

from lark import Lark


from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.types import AbstractionType
from aeon.core.types import TypeVar
from aeon.frontend.parser import TreeToCore
from aeon.sugar.helpers import extract_position
from aeon.sugar.program import Definition
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl


class TreeToSugar(TreeToCore):
    counter: int

    def __init__(self, start_counter=0):
        self.counter = start_counter

    def list(self, args):
        return args

    def program(self, args):
        return Program(imports=args[0], type_decls=args[1], definitions=args[2], source_location=extract_position(args))

    def regular_imp(self, args):
        return ImportAe(path=args[0], func_or_type=[], source_location=extract_position(args))

    def function_imp(self, args):
        return ImportAe(path=args[1], func_or_type=args[0], source_location=extract_position(args))

    def type_decl(self, args):
        return TypeDecl(name=args[0], source_location=extract_position(args))

    def def_cons(self, args):
        return Definition(name=args[0], args=[], type=args[1], body=args[2], source_location=extract_position(args))

    def def_fun(self, args):
        return Definition(
            name=args[0], args=args[1], type=args[2], body=args[3], source_location=extract_position(args)
        )

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


def mk_parser(rule="start", start_counter=0):
    return Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_sugar.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        propagate_positions=True,
        transformer=TreeToSugar(start_counter),
        import_paths=[pathlib.Path(__file__).parent.parent.absolute() / "frontend"],
    )


parse_program = mk_parser("program").parse
