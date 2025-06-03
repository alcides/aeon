from __future__ import annotations

import pathlib
from typing import Callable

from lark import Lark, Transformer, v_args

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
from aeon.sugar.program import InductiveDecl
from aeon.sugar.stypes import (
    SAbstractionType,
    SType,
    STypeConstructor,
    STypeVar,
    SRefinedType,
    STypePolymorphism,
)

from aeon.sugar.ast_helpers import i0
from aeon.sugar.ast_helpers import st_int, st_bool, st_string, st_float, st_unit
from aeon.sugar.stypes import builtin_types
from aeon.utils.name import Name

from aeon.utils.location import FileLocation, Location


def ensure_list(a):
    if isinstance(a, list):
        return a
    else:
        return [a]


class AnnotatedStr(str):
    loc: Location

    def __init__(self, value: str, loc: Location):
        self.loc = loc


class TreeToSugar(Transformer):
    filename: str
    counter: int

    def __init__(self, filename: str, start_counter: int = 0):
        self.filename = filename
        self.counter = start_counter

    def _loc(self, meta):
        return FileLocation(self.filename, start=(meta.line, meta.column), end=(meta.end_line, meta.end_column))

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
            return STypeConstructor(name)
        else:
            name = Name(name_str)
            return STypeVar(name)

    def constructor_t(self, args):
        return STypeConstructor(Name(args[0]), args[1:])

    # Expressions
    @v_args(meta=True)
    def annotation(self, meta, args):
        return SAnnotation(args[0], args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def minus(self, meta, args):
        # TODO: check for length of args instead?
        if isinstance(args[0], SLiteral) and type(args[0]) is int:
            return SLiteral(-args[0].value, args[0].type, loc=self._loc(meta))
        return self.binop([i0, args[0]], "-", meta)

    @v_args(meta=True)
    def let_e(self, meta, args):
        return SLet(Name(args[0]), args[1], args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def rec_e(self, meta, args):
        return SRec(Name(args[0]), args[1], args[2], args[3], loc=self._loc(meta))

    @v_args(meta=True)
    def if_e(self, meta, args):
        return SIf(args[0], args[1], args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def nnot(self, meta, args):
        return SApplication(SVar(Name("!", 0), loc=self._loc(meta)), args[0], loc=self._loc(meta))

    @v_args(meta=True)
    def binop_eq(self, meta, args):
        return self.binop(args, "==", meta)

    @v_args(meta=True)
    def binop_neq(self, meta, args):
        return self.binop(args, "!=", meta)

    @v_args(meta=True)
    def binop_and(self, meta, args):
        return self.binop(args, "&&", meta)

    @v_args(meta=True)
    def binop_or(self, meta, args):
        return self.binop(args, "||", meta)

    @v_args(meta=True)
    def binop_lt(self, meta, args):
        return self.binop(args, "<", meta)

    @v_args(meta=True)
    def binop_le(self, meta, args):
        return self.binop(args, "<=", meta)

    @v_args(meta=True)
    def binop_gt(self, meta, args):
        return self.binop(args, ">", meta)

    @v_args(meta=True)
    def binop_ge(self, meta, args):
        return self.binop(args, ">=", meta)

    @v_args(meta=True)
    def binop_imp(self, meta, args):
        return self.binop(args, "-->", meta)

    @v_args(meta=True)
    def binop_plus(self, meta, args):
        return self.binop(args, "+", meta)

    @v_args(meta=True)
    def binop_minus(self, meta, args):
        return self.binop(args, "-", meta)

    @v_args(meta=True)
    def binop_mult(self, meta, args):
        return self.binop(args, "*", meta)

    @v_args(meta=True)
    def binop_div(self, meta, args):
        return self.binop(args, "/", meta)

    @v_args(meta=True)
    def binop_mod(self, meta, args):
        return self.binop(args, "%", meta)

    def binop(self, args, op: str, meta):
        return SApplication(
            SApplication(SVar(Name(op, 0), loc=self._loc(meta)), args[0], loc=self._loc(meta)),
            args[1],
            loc=self._loc(meta),
        )

    @v_args(meta=True)
    def application_e(self, meta, args):
        return SApplication(args[0], args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def abstraction_e(self, meta, args):
        return SAbstraction(Name(args[0]), args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def tabstraction_e(self, meta, args):
        return STypeAbstraction(Name(args[0]), args[1], args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def type_application_e(self, meta, args):
        return STypeApplication(args[0], args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def var(self, meta, args):
        return SVar(Name(args[0]), loc=self._loc(meta))

    @v_args(meta=True)
    def hole(self, meta, args):
        return SHole(Name(args[0]), loc=self._loc(meta))

    @v_args(meta=True)
    def int_lit(self, meta, args):
        return SLiteral(int(args[0]), type=st_int, loc=self._loc(meta))

    @v_args(meta=True)
    def float_lit(self, meta, args):
        return SLiteral(float(args[0]), type=st_float, loc=self._loc(meta))

    @v_args(meta=True)
    def bool_lit(self, meta, args):
        value = str(args[0]) == "true"
        return SLiteral(value, type=st_bool, loc=self._loc(meta))

    @v_args(meta=True)
    def string_lit(self, meta, args):
        return SLiteral(args[0], type=st_string, loc=self._loc(meta))

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
        non_inductive = [el for el in args[1] if not isinstance(el, InductiveDecl)]
        inductive = [el for el in args[1] if isinstance(el, InductiveDecl)]
        return Program(args[0], non_inductive, inductive, args[2])

    @v_args(meta=True)
    def regular_imp(self, meta, args):
        return ImportAe(args[0], [], loc=self._loc(meta))

    @v_args(meta=True)
    def function_imp(self, meta, args):
        return ImportAe(args[1], args[0], loc=self._loc(meta))

    @v_args(meta=True)
    def type_decl(self, meta, args):
        return TypeDecl(Name(args[0]), [], loc=self._loc(meta))

    @v_args(meta=True)
    def type_constructor_decl(self, meta, args):
        return TypeDecl(Name(args[0]), [Name(i) for i in args[1:]], loc=self._loc(meta))

    @v_args(meta=True)
    def inductive(self, meta, args):
        return InductiveDecl(
            Name(args[0]), [Name(i) for i in args[1]], ensure_list(args[2]), ensure_list(args[3]), loc=self._loc(meta)
        )

    @v_args(meta=True)
    def def_ind_cons(self, meta, args):
        return Definition(Name(args[0]), [], args[1], args[2], SLiteral(None, st_unit), loc=self._loc(meta))

    @v_args(meta=True)
    def def_cons(self, meta, args):
        if len(args) == 3:
            return Definition(Name(args[0]), [], [], args[1], args[2], loc=self._loc(meta))
        else:
            decorators = args[0]
            return Definition(Name(args[1]), [], [], args[2], args[3], decorators, loc=self._loc(meta))

    @v_args(meta=True)
    def def_fun(self, meta, args):
        if len(args) == 4:
            return Definition(Name(args[0]), [], args[1], args[2], args[3], loc=self._loc(meta))
        else:
            decorators = args[0]
            return Definition(Name(args[1]), [], args[2], args[3], args[4], decorators, loc=self._loc(meta))

    def macros(self, args):
        return args

    @v_args(meta=True)
    def macro(self, meta, args):
        return Decorator(Name(args[0]), args[1], loc=self._loc(meta))

    def macro_args(self, args):
        return args

    def empty_list(self, args):
        return []

    def args(self, args):
        return args

    def arg(self, args):
        return (Name(args[0]), args[1])

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


def mk_parser(rule="start", start_counter: int = 0, filename: str = ""):
    parser = Lark.open(
        pathlib.Path(__file__).parent.absolute() / "aeon_sugar.lark",
        parser="lalr",
        # lexer='standard',
        start=rule,
        import_paths=[pathlib.Path(__file__).parent.parent.absolute() / "frontend"],
        propagate_positions=True,
    )
    transf = TreeToSugar(filename, start_counter)

    def parse(s: str):
        tree = parser.parse(s)
        return transf.transform(tree)

    return parse


parse_expression: Callable[[str], STerm] = mk_parser("expression")
parse_program: Callable[[str], Program] = mk_parser("program")
parse_type: Callable[[str], SType] = mk_parser("type")


def parse_main_program(source: str, filename: str) -> Program:
    return mk_parser("program", filename=filename)(source)
