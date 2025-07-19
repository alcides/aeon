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
    def layout(self, context: LayoutContext) -> str:
        return ""

    def fits(self, width: int, current_length: int) -> bool:
        return True

    def best(self, width: int, current_length: int) -> 'Doc':
        return self


@dataclass(frozen=True)
class Text(Doc):
    s: str

    def layout(self, context: LayoutContext) -> str:
        return self.s

    def fits(self, width: int, current_length: int) -> bool:
        return current_length + len(self.s) <= width

    def best(self, width: int, current_length: int) -> 'Doc':
        return self

    def flatten(self) -> 'Doc':
        return self


@dataclass(frozen=True)
class Line(Doc):
    def layout(self, context: LayoutContext) -> str:
        return DEFAULT_NEW_LINE_CHAR + DEFAULT_SPACE_CHAR * context.indent

    def fits(self, width: int, current_length: int) -> bool:
        return True

    def best(self, width: int, current_length: int) -> 'Doc':
        return self

    def flatten(self) -> 'Doc':
        return self


@dataclass(frozen=True)
class Concat(Doc):
    docs: tuple[Doc, ...]
    precedence: int = 0
    assoc: Assoc = Assoc.NONE

    def layout(self, context: LayoutContext) -> str:
        child_size = len(self.docs)
        if child_size == 1:
            child_positions = [Position.NONE]
        elif child_size == 2:
            child_positions = [Position.LEFT, Position.RIGHT]
        elif child_size == 3:
            child_positions = [Position.LEFT, Position.NONE, Position.RIGHT]
        else:
            child_positions = [Position.NONE] * child_size

        layout_string = "".join(
            doc.layout(LayoutContext(indent=context.indent, parent_precedence=self.precedence, position=pos))
            for doc, pos in zip(self.docs, child_positions)
        )
        need_parentheses = False
        if self.precedence < context.parent_precedence:
            need_parentheses = True
        elif self.precedence == parent_precedence:
            if position == Position.LEFT and self.assoc != Assoc.LEFT:
        elif self.precedence == context.parent_precedence:
            if context.position == Position.LEFT and self.assoc != Assoc.LEFT:
                need_parentheses = True
            elif context.position == Position.RIGHT and self.assoc != Assoc.RIGHT:
                need_parentheses = True

        return "(" + layout_string + ")" if need_parentheses else layout_string

    def fits(self, width: int, current_length: int) -> bool:
        curr = current_length
        for doc in self.docs:
            if not doc.fits(width, curr):
                return False
            default_context = LayoutContext(indent=0, parent_precedence=0, position=Position.NONE)
            curr += len(doc.flatten().layout(default_context))
            if curr > width:
                return False
        return True

    def best(self, width: int, current_length: int) -> 'Doc':
        flat = self.flatten()
        if flat.fits(width, current_length):
            return flat
        best_children = []
        curr = current_length
        for doc in self.docs:
            best_child = doc.best(width, curr)
            best_children.append(best_child)
            default_context = LayoutContext(indent=0, parent_precedence=0, position=Position.NONE)
            curr += len(best_child.flatten().layout(default_context))
        return Concat(tuple(best_children), self.precedence, self.assoc)

    def flatten(self) -> 'Doc':
        flattened_children = tuple(doc.flatten() for doc in self.docs)
        return Concat(flattened_children, self.precedence, self.assoc)


@dataclass(frozen=True)
class MultiUnion(Doc):
    alternatives: tuple[Doc, ...]

    def layout(self, context: LayoutContext) -> str:
        return self.best(DEFAULT_WIDTH, context.indent).layout(context)

    def fits(self, width: int, current_length: int) -> bool:
        return any(doc.fits(width, current_length) for doc in self.alternatives)

    def best(self, width: int, current_length: int) -> Doc:
        for doc in self.alternatives:
            if doc.fits(width, current_length):
                return doc
        return self.alternatives[-1]

    def flatten(self):
        return self.alternatives[0].flatten()


@dataclass(frozen=True)
class Nest(Doc):
    indent: int
    doc: Doc
    precedence: int = 0

    def layout(self, context: LayoutContext) -> str:
        s = self.doc.layout(LayoutContext(context.parent_precedence, context.position, context.indent + self.indent))
        lines = s.split(DEFAULT_NEW_LINE_CHAR)
        if not lines:
            return ""
        lines = [(DEFAULT_SPACE_CHAR * self.indent) + line for line in lines]
        return DEFAULT_NEW_LINE_CHAR.join(lines)

    def fits(self, width: int, current_length: int) -> bool:
        s = self.doc.layout(LayoutContext(self.precedence, Position.NONE, 0 + self.indent))
        lines = s.split(DEFAULT_NEW_LINE_CHAR)
        for i, line in enumerate(lines):
            if self.indent + len(line) > width:
                return False
        return True

    def best(self, width: int, current_length: int) -> 'Doc':
        best_doc = self.doc.best(width, current_length)
        return Nest(self.indent, best_doc, self.precedence)

    def flatten(self) -> 'Doc':
        return self.doc.flatten()


def nil() -> Doc:
    return Nil()


def text(s: str) -> Doc:
    if s == "":
        return nil()
    return Text(s)


def line() -> Doc:
    return Line()


def softline() -> Doc:
    return MultiUnion((text(" "), line()))


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
