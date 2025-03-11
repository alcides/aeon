from __future__ import annotations

import pathlib
from typing import Callable

from lark import Lark, Transformer

from aeon.core.types import BaseKind, StarKind
from aeon.sugar.program import (
    Decorator,
    SAbstraction,
    SAnnotation,
    SApplication,
    SHole,
    SIf,
    SLet,
    SLiteral,
    SRec,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
)
from aeon.sugar.program import Definition
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl
from aeon.sugar.stypes import (
    SAbstractionType,
    SBaseType,
    SType,
    STypeConstructor,
    STypeVar,
    SRefinedType,
    STypePolymorphism,
)

from aeon.sugar.ast_helpers import i0
from aeon.sugar.ast_helpers import mk_binop
from aeon.sugar.stypes import builtin_types


class TreeToSugar(Transformer):

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
        return SRefinedType(str(args[0]), args[1], args[2])

    def abstraction_t(self, args):
        return SAbstractionType(str(args[0]), args[1], args[2])

    def polymorphism_t(self, args):
        return STypePolymorphism(str(args[0]), args[1], args[2])

    def simple_t(self, args):
        name = str(args[0])
        if name in builtin_types:
            return SBaseType(name)
        else:
            return STypeVar(str(args[0]))

    def constructor_t(self, args):
        return STypeConstructor(str(args[0]), args[1:])

    # Expressions

    def annotation(self, args):
        return SAnnotation(args[0], args[1])

    def minus(self, args):
        # TODO: check for length of args instead?
        if isinstance(args[0], SLiteral) and type(args[0]) is int:
            return SLiteral(-args[0].value, args[0].type)
        return mk_binop(lambda: self.fresh(), "-", i0, args[0])

    def let_e(self, args):
        return SLet(str(args[0]), args[1], args[2])

    def rec_e(self, args):
        return SRec(str(args[0]), args[1], args[2], args[3])

    def if_e(self, args):
        return SIf(args[0], args[1], args[2])

    def nnot(self, args):
        return SApplication(SVar("!"), args[0])

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
        return SApplication(args[0], args[1])

    def abstraction_e(self, args):
        return SAbstraction(str(args[0]), args[1])

    def tabstraction_e(self, args):
        return STypeAbstraction(str(args[0]), args[1], args[2])

    def type_application_e(self, args):
        return STypeApplication(args[0], args[1])

    def var(self, args):
        return SVar(str(args[0]).strip())

    def hole(self, args):
        return SHole(str(args[0]))

    def int_lit(self, args):
        return SLiteral(int(args[0]), type=SBaseType("Int"))

    def float_lit(self, args):
        return SLiteral(float(args[0]), type=SBaseType("Float"))

    def bool_lit(self, args):
        value = str(args[0]) == "true"
        return SLiteral(value, type=SBaseType("Bool"))

    def string_lit(self, args):
        return SLiteral(args[0], type=SBaseType("String"))

    def ESCAPED_STRING(self, val):
        # TODO: This is terrible and doesn't handle escapes
        v = str(val)[1:-1]
        return v

    def base_kind(self, args):
        return BaseKind()

    def star_kind(self, args):
        return StarKind()

    def list(self, args):
        return args

    def program(self, args):
        return Program(args[0], args[1], args[2])

    def regular_imp(self, args):
        return ImportAe(args[0], [])

    def function_imp(self, args):
        return ImportAe(args[1], args[0])

    def type_decl(self, args):
        return TypeDecl(str(args[0]), [])

    def type_constructor_decl(self, args):
        return TypeDecl(str(args[0]), [str(i) for i in args[1:]])

    def def_cons(self, args):
        if len(args) == 3:
            return Definition(str(args[0]), [], [], args[1], args[2])
        else:
            decorators = args[0]
            return Definition(str(args[1]), [], [], args[2], args[3],
                              decorators)

    def def_fun(self, args):
        if len(args) == 4:
            return Definition(str(args[0]), [], args[1], args[2], args[3])
        else:
            decorators = args[0]
            return Definition(str(args[1]), [], args[2], args[3], args[4],
                              decorators)

    def macros(self, args):
        return args

    def macro(self, args):
        return Decorator(str(args[0]), args[1])

    def macro_args(self, args):
        return args

    def empty_list(self, args):
        return []

    def args(self, args):
        return args

    def arg(self, args):
        return (str(args[0]), args[1])

    def refined_arg(self, args):
        return str(args[0]), SRefinedType(str(args[0]), args[1], args[2])

    def abstraction_refined_t(self, args):
        type = SRefinedType(str(args[0]), args[1], args[2])
        return SAbstractionType(str(args[0]), type, args[3])

    def abstraction_et(self, args):
        return SAnnotation(
            SAbstraction(str(args[0]), args[2]),
            SAbstractionType(str(args[0]), args[1],
                             STypeVar("?t")),  # TODO NOW: understand this?
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


parse_expression: Callable[[str], STerm] = mk_parser("expression").parse
parse_program: Callable[[str], Program] = mk_parser("program").parse
parse_type: Callable[[str], SType] = mk_parser("type").parse
