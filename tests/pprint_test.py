from abc import abstractmethod, ABC
from dataclasses import dataclass

from aeon.utils.pprint_helpers import Doc, text, concat, Assoc, LayoutContext, Position


def test_simple_pprint_1():
    expr = Mul(Add(Num(1), Num(2)), Div(Num(3), Num(4)))
    expected = "(1 + 2) * (3 / 4)"
    assert expected == expr.to_doc().best(0, 0).layout(context=LayoutContext(0, Position.NONE, 0))


def test_simple_pprint_2():
    expr = Div(Add(Mul(Num(1), Num(2)), Num(2)), Div(Num(3), Num(4)))
    expected = "(1 * 2 + 2) / (3 / 4)"
    assert expected == expr.to_doc().best(0, 0).layout(context=LayoutContext(0, Position.NONE, 0))


def test_complex_pretty_print():
    expr = Div(
        Sub(Add(Num(1), Mul(Sub(Num(2), Num(3)), Num(4))), Div(Num(5), Num(6))), Add(Num(7), Mul(Num(8), Num(9)))
    )
    expected = "(1 + (2 - 3) * 4 - 5 / 6) / (7 + 8 * 9)"
    assert expected == expr.to_doc().best(0, 0).layout(context=LayoutContext(0, Position.NONE, 0))


# helper classes
class Expr(ABC):
    @abstractmethod
    def to_doc(self) -> Doc: ...


@dataclass(frozen=True)
class Num(Expr):
    val: int

    def to_doc(self) -> Doc:
        return text(str(self.val))


@dataclass(frozen=True)
class Add(Expr):
    left: Expr
    right: Expr

    def to_doc(self) -> Doc:
        return concat([self.left.to_doc(), text(" + "), self.right.to_doc()], precedence=1, assoc=Assoc.LEFT)


@dataclass(frozen=True)
class Sub(Expr):
    left: Expr
    right: Expr

    def to_doc(self) -> Doc:
        return concat([self.left.to_doc(), text(" - "), self.right.to_doc()], precedence=1, assoc=Assoc.LEFT)


@dataclass(frozen=True)
class Mul(Expr):
    left: Expr
    right: Expr

    def to_doc(self) -> Doc:
        return concat([self.left.to_doc(), text(" * "), self.right.to_doc()], precedence=2, assoc=Assoc.LEFT)


@dataclass(frozen=True)
class Div(Expr):
    left: Expr
    right: Expr

    def to_doc(self) -> Doc:
        return concat([self.left.to_doc(), text(" / "), self.right.to_doc()], precedence=2, assoc=Assoc.LEFT)
