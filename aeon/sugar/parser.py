from __future__ import annotations

import pathlib

from lark import Lark
from lark import Transformer

from aeon.core.substitutions import liquefy
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.core.types import TypeVar
from aeon.frontend.parser import TreeToCore
from aeon.sugar.program import Definition
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl
from aeon.utils.ast_helpers import ensure_anf_app
from aeon.utils.ast_helpers import ensure_anf_if
from aeon.utils.ast_helpers import ensure_anf_let
from aeon.utils.ast_helpers import ensure_anf_rec
from aeon.utils.ast_helpers import i0
from aeon.utils.ast_helpers import mk_binop


class TreeToSugar(TreeToCore):

    def list(self, args):
        return args

    def program(self, args):
        return Program(args[0], args[1])

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


def mk_parser(rule="start", start_counter=0):
    return Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_sugar.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        transformer=TreeToSugar(start_counter),
        import_paths=[
            pathlib.Path(__file__).parent.parent.absolute() / "frontend"
        ],
    )


parse_program = mk_parser("program").parse
