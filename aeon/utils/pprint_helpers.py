from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum

from aeon.sugar.program import SLiteral, SVar, STerm, SAnnotation, SApplication, SAbstraction, SLet, SRec, SIf, \
    STypeAbstraction, STypeApplication, SHole
from aeon.sugar.stypes import STypeConstructor, STypePolymorphism, SAbstractionType, SRefinedType, STypeVar, SType
from aeon.utils.name import Name

DEFAULT_NEW_LINE_CHAR = "\n"
DEFAULT_SPACE_CHAR = " "
DEFAULT_WIDTH = 80
DEFAULT_TAB_SIZE = 4


class Assoc(Enum):
    LEFT = "left"
    RIGHT = "right"
    NONE = "none"


class Position(Enum):
    LEFT = "left"
    RIGHT = "right"
    NONE = "none"


POLYMORPHISM_PRECEDENCE = 5
LET_PRECEDENCE = 10
IF_PRECEDENCE = 10
ARROW_PRECEDENCE = 15
LAMBDA_PRECEDENCE = 20
REFINED_TYPE_PRECEDENCE = 25
ANNOTATION_PRECEDENCE = 30
TYPE_CONSTRUCTOR_PRECEDENCE = 35
APPLICATION_PRECEDENCE = 40
TYPE_APPLICATION_PRECEDENCE = 45
LITERAL_PRECEDENCE = 100


@dataclass(frozen=True)
class LayoutContext:
    parent_precedence: int
    position: Position
    indent: int = 0


class Doc(ABC):
    @abstractmethod
    def layout(self, context: LayoutContext) -> str: ...

    @abstractmethod
    def fits(self, width: int, current_length: int) -> bool:
        ...

    @abstractmethod
    def best(self, width: int, current_length: int) -> 'Doc':
        ...

    def flatten(self) -> 'Doc':
        return self

    def __str__(self):
        return self.best(DEFAULT_WIDTH, 0).layout(LayoutContext(0, Position.NONE, 0))


@dataclass(frozen=True)
class Nil(Doc):
    def layout(self, indent=0, parent_precedence=0, position: Position = Position.NONE) -> str:
        return ""


@dataclass(frozen=True)
class Text(Doc):
    s: str
    precedence: int = 0

    def layout(self, indent=0, parent_precedence=0, position: Position = Position.NONE) -> str:
        return self.s


@dataclass(frozen=True)
class Line(Doc):
    def layout(self, indent=0, parent_precedence=0, position: Position = Position.NONE) -> str:
        return "\n" + " " * indent


@dataclass(frozen=True)
class Concat(Doc):
    docs: tuple[Doc, ...]
    precedence: int = 0
    assoc: Assoc = Assoc.NONE

    def layout(self, indent=0, parent_precedence=0, position: Position = Position.NONE) -> str:
        child_size = len(self.docs)
        child_positions = (
            [Position.LEFT, Position.NONE, Position.RIGHT] if child_size == 3 else [Position.NONE] * child_size
        )

        s = "".join(doc.layout(indent, self.precedence, pos) for doc, pos in zip(self.docs, child_positions))

        need_parentheses = False
        if self.precedence < parent_precedence:
            need_parentheses = True
        elif self.precedence == parent_precedence:
            if position == Position.LEFT and self.assoc != Assoc.LEFT:
                need_parentheses = True
            elif position == Position.RIGHT and self.assoc != Assoc.RIGHT:
                need_parentheses = True

        return "(" + s + ")" if need_parentheses else s


@dataclass(frozen=True)
class Nest(Doc):
    indent: int
    doc: Doc
    precedence: int = 0

    def layout(self, indent=0, parent_precedence=0, position: Position = Position.NONE) -> str:
        s = self.doc.layout(indent + self.indent, parent_precedence, position)
        lines = s.split("\n")
        indented_lines = [(" " * self.indent) + line for line in lines]
        return "\n".join(indented_lines)


@dataclass(frozen=True)
class Group(Doc):
    doc: Doc

    def layout(self, indent=0, parent_precedence=0, position: Position = Position.NONE) -> str:
        return self.doc.layout(indent, parent_precedence, position)


def nil() -> Doc:
    return Nil()


def text(s: str, precedence=0) -> Doc:
    if s == "":
        return nil()
    return Text(s, precedence)


def line() -> Doc:
    return Line()


def concat(docs: list[Doc], precedence: int, assoc: Assoc = Assoc.NONE) -> Doc:
    filtered = [d for d in docs if not isinstance(d, Nil)]
    if not filtered:
        return nil()
    if len(filtered) == 1:
        return filtered[0]
    return Concat(tuple(filtered), precedence, assoc)


def nest(i: int, doc: Doc) -> Doc:
    return Nest(i, doc)


def group(doc: Doc) -> Doc:
    return Group(doc)
