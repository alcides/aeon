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
from aeon.core.terms import Abstraction, Application, Let, Term, Var, Literal, If
from aeon.utils.ast_helpers import mk_binop, i0


class TreeToCore(Transformer):
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

    def minus(self, args):
        return mk_binop("-", i0, args[0])

    def let_e(self, args):
        return Let(str(args[0]), args[1], args[2])

    def if_e(self, args):
        return If(*args)

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
        return mk_binop(op, args[0], args[1])

    def application_e(self, args):
        return Application(*args)

    def abstraction_e(self, args):
        args[0] = str(args[0])
        return Abstraction(*args)

    def var(self, args):
        return Var(str(args[0]))

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


def mk_parser(rule="start"):
    return Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_core.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        transformer=TreeToCore(),
    )


parse_type: Type = mk_parser("type").parse
parse_term: Term = mk_parser("expression").parse
