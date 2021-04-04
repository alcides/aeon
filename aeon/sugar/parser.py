from aeon.utils.ast_helpers import mk_binop
import pathlib
from lark import Lark, Transformer

from aeon.frontend.parser import TreeToCore
from aeon.core.substitutions import liquefy
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    Term,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    BaseType,
    RefinedType,
    t_int,
    t_bool,
    t_string,
    t_float,
)
from aeon.utils.ast_helpers import (
    ensure_anf_let,
    ensure_anf_if,
    ensure_anf_app,
    ensure_anf_rec,
    mk_binop,
    i0,
)

from aeon.sugar.program import Program, TypeDecl, Definition


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


def mk_parser(rule="start", start_counter=0):
    return Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_sugar.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        transformer=TreeToSugar(start_counter),
        import_paths=[pathlib.Path(__file__).parent.parent.absolute() / "frontend"],
    )


parse_program: Term = mk_parser("program").parse
