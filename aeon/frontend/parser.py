from typing import Callable
from aeon.utils.ast_helpers import mk_binop
from aeon.core.substitutions import liquefy
import os
import pathlib

from lark import Lark, Transformer

from aeon.core.types import (
    AbstractionType,
    RefinedType,
    BaseType,
    Type,
    t_int,
    t_bool,
    t_float,
    t_string,
)
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Let,
    Rec,
    Term,
    Var,
    Literal,
    If,
    Hole,
)
from aeon.utils.ast_helpers import (
    ensure_anf_let,
    ensure_anf_if,
    ensure_anf_app,
    mk_binop,
    i0,
)


class TreeToCore(Transformer):
    counter: int

    def __init__(self, start_counter=0):
        self.counter = start_counter

    def fresh(self) -> str:
        self.counter += 1
        return "_anf_{}".format(self.counter)

    def same(self, args):
        return args[0]

    # Types
    def refined_t(self, args):
        return RefinedType(str(args[0]), args[1], liquefy(args[2]))

    def abstraction_t(self, args):
        return AbstractionType(str(args[0]), args[1], args[2])

    def simple_t(self, args):
        return BaseType(str(args[0]))

    # Expressions

    def annotation(self, args):
        return Annotation(args[0], args[1])

    def minus(self, args):
        if isinstance(args[0], Literal) and args[0].type == t_int:
            return Literal(-args[0].value, args[0].type)
        return mk_binop(lambda: self.fresh(), "-", i0, args[0])

    def let_e(self, args):
        return ensure_anf_let(Let(str(args[0]), args[1], args[2]))

    def rec_e(self, args):
        return Rec(str(args[0]), args[1], args[2], args[3])

    def if_e(self, args):
        return ensure_anf_if(lambda: self.fresh(), If(args[0], args[1], args[2]))

    def nnot(self, args):
        return Application(Var("!"), args[0])

    def binop_eq(self, args):
        return self.binop(args, "==")

    def binop_neq(self, args):
        return self.binop(args, "!=")

    def binop_and(self, args):
        return self.binop(args, "&&")

    def binop_or(self, args):
        return self.binop(args, "||")

    def binop_lt(self, args):
        return self.binop(args, "<")

    def binop_le(self, args):
        return self.binop(args, "<=")

    def binop_gt(self, args):
        return self.binop(args, ">")

    def binop_ge(self, args):
        return self.binop(args, ">=")

    def binop_imp(self, args):
        return self.binop(args, "-->")

    def binop_plus(self, args):
        return self.binop(args, "+")

    def binop_minus(self, args):
        return self.binop(args, "-")

    def binop_mult(self, args):
        return self.binop(args, "*")

    def binop_div(self, args):
        return self.binop(args, "/")

    def binop_mod(self, args):
        return self.binop(args, "%")

    def binop(self, args, op):
        return mk_binop(lambda: self.fresh(), op, args[0], args[1])

    def application_e(self, args):
        return ensure_anf_app(lambda: self.fresh(), Application(args[0], args[1]))

    def abstraction_e(self, args):
        return Abstraction(str(args[0]), args[1])

    def var(self, args):
        return Var(str(args[0]))

    def hole(self, args):
        return Hole(str(args[0]))

    def fitness_annotation(self, args):
        return Var(str(args[0]))

    def int_lit(self, args):
        return Literal(int(args[0]), type=t_int)

    def float_lit(self, args):
        return Literal(float(args[0]), type=t_float)

    def bool_lit(self, args):
        value = str(args[0]) == "true"
        return Literal(value, type=t_bool)

    def string_lit(self, args):
        v = str(args[0])[1:-1]
        return Literal(str(v), type=t_string)


def mk_parser(rule="start", start_counter=0):
    return Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_core.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        transformer=TreeToCore(start_counter),
    )


parse_type: Type = mk_parser("type").parse
parse_term: Term = mk_parser("expression").parse
