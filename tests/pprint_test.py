from abc import abstractmethod, ABC
from dataclasses import dataclass
from enum import IntEnum

from aeon.utils.pprint_helpers import (
    Doc,
    text,
    concat,
    Associativity,
    Side,
    parens,
    needs_parens_aux,
)


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


# Helper Classes


class Precedence(IntEnum):
    ADD = 1
    SUB = 1
    MUL = 2
    DIV = 2
    NUM = 3


@dataclass(frozen=True)
class ParenthesisContext:
    parent_precedence: Precedence
    child_side: Side


class Expr(ABC):
    @abstractmethod
    def to_doc(self, parenthesis_context: ParenthesisContext = None) -> Doc: ...

    def precedence(self) -> Precedence:
        return Precedence.NUM

    def associativity(self) -> Associativity:
        return Associativity.NONE


@dataclass(frozen=True)
class Num(Expr):
    val: int

    def to_doc(self, parenthesis_context: ParenthesisContext = None) -> Doc:
        if parenthesis_context is None:
            parenthesis_context = ParenthesisContext(parent_precedence=Precedence.ADD, child_side=Side.NONE)
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
            parenthesis_context = ParenthesisContext(parent_precedence=Precedence.ADD, child_side=Side.NONE)
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
    _precedence = Precedence.ADD


@dataclass(frozen=True)
class Sub(BinOp):
    symbol = "-"
    _precedence = Precedence.SUB


@dataclass(frozen=True)
class Mul(BinOp):
    symbol = "*"
    _precedence = Precedence.MUL


@dataclass(frozen=True)
class Div(BinOp):
    symbol = "/"
    _precedence = Precedence.DIV
