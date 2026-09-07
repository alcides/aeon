from abc import abstractmethod, ABC
from dataclasses import dataclass

from aeon.sugar.lifting import lift_type
from aeon.sugar.lowering import type_to_core
from aeon.sugar.parser import parse_type
from aeon.utils.pprint import Associativity, Side, needs_parens_aux, ParenthesisContext, Precedence, stype_pretty
from aeon.utils.pprint_helpers import (
    Doc,
    text,
    concat,
    parens,
)


def test_refinement_comparison_operand_order():
    # Regression: lift_liquid reversed curried application args, so a refinement
    # written `y >= 5` printed as `5 >= y` after a round-trip through the core AST.
    # The pretty-printer emits the Unicode ``≥``.
    sugar_ty = parse_type("{y:Int | y >= 5}")
    core_ty = type_to_core(sugar_ty)
    rendered = str(stype_pretty(lift_type(core_ty)))
    assert "y ≥ 5" in rendered
    assert "5 ≥ y" not in rendered


def test_pretty_param_inlines_mismatched_refinement_binder():
    from aeon.utils.name import Name
    from aeon.utils.pprint import pretty_print_param

    ty = parse_type("{n:Int | n >= 0}")
    rendered = pretty_print_param(Name("id", 0), ty)
    assert rendered == "(id : Int | id ≥ 0)" or rendered.replace(" ", "") == "(id:Int|id≥0)"
    assert "n" not in rendered.split("|")[1]


def test_simple_pprint_1():
    expr = Mul(Add(Num(1), Num(2)), Div(Num(3), Num(4)))
    expected = "(1 + 2) * (3 / 4)"
    assert expected == expr.to_doc().best(80, 0).layout(0)


def test_simple_pprint_2():
    expr = Div(Add(Mul(Num(1), Num(2)), Num(2)), Div(Num(3), Num(4)))
    expected = "(1 * 2 + 2) / (3 / 4)"
    assert expected == expr.to_doc().best(80, 0).layout(0)


def test_complex_pretty_print():
    expr = Div(
        Sub(Add(Num(1), Mul(Sub(Num(2), Num(3)), Num(4))), Div(Num(5), Num(6))), Add(Num(7), Mul(Num(8), Num(9)))
    )
    expected = "(1 + (2 - 3) * 4 - 5 / 6) / (7 + 8 * 9)"
    assert expected == expr.to_doc().best(80, 0).layout(0)


def test_operator_section_prints_parseably():
    # A bare operator variable prints as an operator section so the output
    # re-parses (e.g. `let v : ... := (=) in ...`).
    from aeon.sugar.program import SVar
    from aeon.utils.name import Name
    from aeon.utils.pprint import pretty_print_sterm

    assert pretty_print_sterm(SVar(Name("==", 0)), top_level=False) == "(=)"
    assert pretty_print_sterm(SVar(Name("+", 0)), top_level=False) == "(+)"
    assert pretty_print_sterm(SVar(Name("<=", 0)), top_level=False) == "(≤)"
    assert pretty_print_sterm(SVar(Name("&&", 0)), top_level=False) == "(&&)"


def test_operator_section_parses():
    from aeon.sugar.parser import mk_parser
    from aeon.sugar.program import SVar

    parse_expr = mk_parser("expression")
    for source, op in [("(=)", "=="), ("(==)", "=="), ("(+)", "+"), ("(≤)", "<="), ("(<=)", "<="), ("(||)", "||")]:
        term = parse_expr(source)
        assert isinstance(term, SVar)
        assert term.name.pretty() == op
    # Parenthesised expressions are unaffected.
    assert not isinstance(parse_expr("(- 1)"), SVar)
    assert not isinstance(parse_expr("(x = y)"), SVar)


def test_negative_literal_operand_parenthesized():
    # Unary minus only exists at the outermost expression level in the grammar,
    # so a negative literal operand must print parenthesised to re-parse:
    # `9 - -1` and `f -1` are syntax errors.
    from aeon.sugar.parser import mk_parser
    from aeon.utils.pprint import pretty_print_sterm

    parse_expr = mk_parser("expression")
    for source in ["9 - (-1)", "9 * (-1)", "f (-1)", "(-1) + 2", "(-1.5) + x"]:
        printed = pretty_print_sterm(parse_expr(source), top_level=False)
        assert printed == source
        parse_expr(printed)


def test_operator_section_round_trips():
    from aeon.sugar.parser import mk_parser
    from aeon.sugar.program import SVar
    from aeon.utils.name import Name
    from aeon.utils.pprint import pretty_print_sterm

    parse_expr = mk_parser("expression")
    for op in ["==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/", "%", "&&", "||"]:
        printed = pretty_print_sterm(SVar(Name(op, 0)), top_level=False)
        reparsed = parse_expr(printed)
        assert isinstance(reparsed, SVar)
        assert reparsed.name.pretty() == op


# Helper Classes


class Expr(ABC):
    @abstractmethod
    def to_doc(self, parenthesis_context: ParenthesisContext = None) -> Doc: ...

    def precedence(self) -> Precedence:
        return Precedence.LITERAL

    def associativity(self) -> Associativity:
        return Associativity.NONE


@dataclass(frozen=True)
class Num(Expr):
    val: int

    def to_doc(self, parenthesis_context: ParenthesisContext = None) -> Doc:
        if parenthesis_context is None:
            parenthesis_context = ParenthesisContext(parent_precedence=Precedence.LITERAL, child_side=Side.NONE)
        return text(str(self.val))


@dataclass(frozen=True)
class BinOp(Expr, ABC):
    left: Expr
    right: Expr

    @property
    @abstractmethod
    def symbol(self) -> str: ...

    @property
    @abstractmethod
    def _precedence(self) -> Precedence: ...

    def associativity(self) -> Associativity:
        return Associativity.LEFT

    def precedence(self) -> Precedence:
        return self._precedence

    def to_doc(self, parenthesis_context: ParenthesisContext = None) -> Doc:
        if parenthesis_context is None:
            parenthesis_context = ParenthesisContext(parent_precedence=Precedence.LITERAL, child_side=Side.NONE)
        left_doc = self.left.to_doc(ParenthesisContext(self.precedence(), Side.LEFT))
        if needs_parens_aux(self.left.associativity(), self.left.precedence(), Side.LEFT, self._precedence):
            left_doc = parens(left_doc)
        right_doc = self.right.to_doc(ParenthesisContext(self.precedence(), Side.RIGHT))
        if needs_parens_aux(self.right.associativity(), self.right.precedence(), Side.RIGHT, self._precedence):
            right_doc = parens(right_doc)
        return concat([left_doc, text(f" {self.symbol} "), right_doc])


@dataclass(frozen=True)
class Add(BinOp):
    symbol = "+"
    _precedence = Precedence.INFIX_ADDITIVE


@dataclass(frozen=True)
class Sub(BinOp):
    symbol = "-"
    _precedence = Precedence.INFIX_ADDITIVE


@dataclass(frozen=True)
class Mul(BinOp):
    symbol = "*"
    _precedence = Precedence.INFIX_MULTIPLICATIVE


@dataclass(frozen=True)
class Div(BinOp):
    symbol = "/"
    _precedence = Precedence.INFIX_MULTIPLICATIVE
