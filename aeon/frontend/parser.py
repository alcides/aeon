from __future__ import annotations

import pathlib
from typing import Callable

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
from aeon.core.terms import Maximize
from aeon.core.terms import Minimize
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import TypeAbstraction
from aeon.core.terms import TypeApplication
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import BaseKind
from aeon.core.types import BaseType
from aeon.core.types import bottom
from aeon.core.types import RefinedType
from aeon.core.types import StarKind
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.core.types import top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.utils.ast_helpers import ensure_anf_app
from aeon.utils.ast_helpers import ensure_anf_if
from aeon.utils.ast_helpers import ensure_anf_let
from aeon.utils.ast_helpers import ensure_anf_rec
from aeon.utils.ast_helpers import i0
from aeon.utils.ast_helpers import mk_binop


class TreeToCore(Transformer):
    counter: int

    def __init__(self, start_counter=0):
        self.counter = start_counter

    def fresh(self) -> str:
        self.counter += 1
        return f"_anf_{self.counter}"

    def same(self, args):
        return args[0]

    # Types
    def refined_t(self, args):
        return RefinedType(str(args[0]), args[1], liquefy(args[2]))

    def abstraction_t(self, args):
        return AbstractionType(str(args[0]), args[1], args[2])

    def polymorphism_t(self, args):
        return TypePolymorphism(str(args[0]), args[1], args[2])

    def simple_t(self, args):
        n = str(args[0])
        if n == "Bottom":
            return bottom
        elif n == "Top":
            return top
        elif n in ["Unit", "Int", "Bool", "Float", "String"]:
            return BaseType(n)
        else:
            return TypeVar(n)

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
        return ensure_anf_rec(Rec(str(args[0]), args[1], args[2], args[3]))

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

    def binop_plus_f(self, args):
        return self.binop(args, "+.")

    def binop_minus_f(self, args):
        return self.binop(args, "-.")

    def binop_mult_f(self, args):
        return self.binop(args, "*.")

    def binop_div_f(self, args):
        return self.binop(args, "/.")

    def binop_mod_f(self, args):
        return self.binop(args, "%.")

    def binop(self, args, op):
        return mk_binop(lambda: self.fresh(), op, args[0], args[1])

    def application_e(self, args):
        return ensure_anf_app(lambda: self.fresh(), Application(args[0], args[1]))

    def abstraction_e(self, args):
        return Abstraction(str(args[0]), args[1])

    def tabstraction_e(self, args):
        return TypeAbstraction(str(args[0]), args[1], args[2])

    def type_application_e(self, args):
        return TypeApplication(args[0], args[1])

    def var(self, args):
        return Var(str(args[0]).strip())

    def hole(self, args):
        return Hole(str(args[0]))

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

    def base_kind(self, args):
        return BaseKind()

    def star_kind(self, args):
        return StarKind()

    def expression_min(self, args):
        return Minimize(args[0])

    def expression_max(self, args):
        return Maximize(args[0])


def mk_parser(rule="start", start_counter=0):
    return Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_core.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        transformer=TreeToCore(start_counter),
    )


parse_type: Callable[[str], Type] = mk_parser("type").parse
parse_term: Callable[[str], Term] = mk_parser("expression").parse
