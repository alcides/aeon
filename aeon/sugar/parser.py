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
from aeon.sugar.ast_helpers import st_int, st_bool, st_string, st_float
from aeon.sugar.stypes import builtin_types
from aeon.utils.name import Name


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
        return SRefinedType(Name(args[0]), args[1], args[2])

    def abstraction_t(self, args):
        return SAbstractionType(Name(args[0]), args[1], args[2])

    def polymorphism_t(self, args):
        return STypePolymorphism(Name(args[0]), args[1], args[2])

    def simple_t(self, args):
        name_str = str(args[0])
        if name_str in builtin_types:
            name = Name(name_str, 0)
            return SBaseType(name)
        else:
            name = Name(name_str)
            return STypeVar(name)

    def constructor_t(self, args):
        return STypeConstructor(Name(args[0]), args[1:])

    # Expressions

    def annotation(self, args):
        return SAnnotation(args[0], args[1])

    def minus(self, args):
        # TODO: check for length of args instead?
        if isinstance(args[0], SLiteral) and type(args[0]) is int:
            return SLiteral(-args[0].value, args[0].type)
        return mk_binop(lambda: self.fresh(), Name("-", 0), i0, args[0])

    def let_e(self, args):
        return SLet(Name(args[0]), args[1], args[2])

    def rec_e(self, args):
        return SRec(Name(args[0]), args[1], args[2], args[3])

    def if_e(self, args):
        return SIf(args[0], args[1], args[2])

    def nnot(self, args):
        return SApplication(SVar(Name("!", 0)), args[0])

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
        return mk_binop(lambda: self.fresh(), Name(op, 0), args[0], args[1])

    def application_e(self, args):
        return SApplication(args[0], args[1])

    def abstraction_e(self, args):
        return SAbstraction(Name(args[0]), args[1])

    def tabstraction_e(self, args):
        return STypeAbstraction(Name(args[0]), args[1], args[2])

    def type_application_e(self, args):
        return STypeApplication(args[0], args[1])

    def var(self, args):
        return SVar(Name(args[0]))

    def hole(self, args):
        return SHole(Name(args[0]))

    def int_lit(self, args):
        return SLiteral(int(args[0]), type=st_int)

    def float_lit(self, args):
        return SLiteral(float(args[0]), type=st_float)

    def bool_lit(self, args):
        value = str(args[0]) == "true"
        return SLiteral(value, type=st_bool)

    def string_lit(self, args):
        return SLiteral(args[0], type=st_string)

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
        return TypeDecl(Name(args[0]), [])

    def type_constructor_decl(self, args):
        return TypeDecl(Name(args[0]), [Name(i) for i in args[1:]])

    def def_cons(self, args):
        if len(args) == 3:
            return Definition(Name(args[0]), [], [], args[1], args[2])
        else:
            decorators = args[0]
            return Definition(Name(args[1]), [], [], args[2], args[3], decorators)

    def def_fun(self, args):
        if len(args) == 4:
            return Definition(Name(args[0]), [], args[1], args[2], args[3])
        else:
            decorators = args[0]
            return Definition(Name(args[1]), [], args[2], args[3], args[4], decorators)

    def macros(self, args):
        return args

    def macro(self, args):
        return Decorator(Name(args[0]), args[1])

    def macro_args(self, args):
        return args

    def empty_list(self, args):
        return []

    def args(self, args):
        return args

    def arg(self, args):
        return (str(args[0]), args[1])

    def refined_arg(self, args):
        return Name(args[0]), SRefinedType(Name(args[0]), args[1], args[2])

    def abstraction_refined_t(self, args):
        type = SRefinedType(Name(args[0]), args[1], args[2])
        return SAbstractionType(Name(args[0]), type, args[3])

    def abstraction_et(self, args):
        return SAnnotation(
            SAbstraction(Name(args[0]), args[2]),
            SAbstractionType(Name(args[0]), args[1], STypeVar(Name("?t"))),  # TODO NOW: understand this?
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


parse_expression: Callable[[str], STerm] = mk_parser("expression").parse
parse_program: Callable[[str], Program] = mk_parser("program").parse
parse_type: Callable[[str], SType] = mk_parser("type").parse
