from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Callable, Iterable

DEFAULT_NEW_LINE_CHAR = "\n"
DEFAULT_SPACE_CHAR = " "
DEFAULT_WIDTH = 120
DEFAULT_TAB_SIZE = 4


class Doc(ABC):
    @abstractmethod
    def layout(self, indent: int) -> str: ...

    @abstractmethod
    def fits(self, width: int, current_length: int) -> bool: ...

    @abstractmethod
    def best(self, width: int, current_length: int) -> "Doc": ...

    @abstractmethod
    def flatten(self) -> "Doc": ...

    def __str__(self):
        return self.best(DEFAULT_WIDTH, 0).layout(0)

    def __add__(self, other):
        return Concat(self, other)

    def calculate_new_length(self, current_length: int) -> int:
        match self:
            case Line():
                return 0
            case Text(value):
                return current_length + len(value)
            case _:
                layout = self.layout(0)
                if DEFAULT_NEW_LINE_CHAR in layout:
                    last_line = layout.rsplit(DEFAULT_NEW_LINE_CHAR, 1)[-1]
                    return len(last_line)
                else:
                    return current_length + len(layout)


@dataclass(frozen=True)
class Nil(Doc):
    def layout(self, _) -> str:
        return ""

    def fits(self, *_) -> bool:
        return True

    def best(self, *_) -> "Doc":
        return self

    def flatten(self) -> "Doc":
        return self


@dataclass(frozen=True)
class Text(Doc):
    value: str

    def layout(self, _) -> str:
        return self.value

    def fits(self, width: int, current_length: int) -> bool:
        return current_length + len(self.value) <= width

    def best(self, *_) -> "Doc":
        return self

    def flatten(self) -> "Doc":
        return self


@dataclass(frozen=True)
class Line(Doc):
    def layout(self, indent: int) -> str:
        return DEFAULT_NEW_LINE_CHAR + DEFAULT_SPACE_CHAR * indent

    def fits(self, width: int, current_length: int) -> bool:
        return current_length + 1 <= width

    def best(self, *_) -> "Doc":
        return self

    def flatten(self) -> "Doc":
        return Text(DEFAULT_SPACE_CHAR)


@dataclass(frozen=True)
class SoftLine(Line):
    def fits(self, width: int, current_length: int) -> bool:
        return current_length <= width

    def flatten(self) -> "Doc":
        return Text("")


@dataclass(frozen=True)
class HardLine(Line):
    def fits(self, *_) -> bool:
        return False

    def flatten(self) -> "Doc":
        return self


@dataclass(frozen=True)
class Concat(Doc):
    left: Doc
    right: Doc

    def layout(self, indent: int) -> str:
        return self.left.layout(indent) + self.right.layout(indent)

    def fits(self, width: int, current_length: int) -> bool:
        if not self.left.fits(width, current_length):
            return False

        new_length = self.left.calculate_new_length(current_length)

        return self.right.fits(width, new_length)

    def best(self, width: int, current_length: int) -> "Doc":
        left_best = self.left.best(width, current_length)

        new_length = left_best.calculate_new_length(current_length)

        right_best = self.right.best(width, new_length)
        return Concat(left_best, right_best)

    def flatten(self) -> "Doc":
        return self.left.flatten() + self.right.flatten()


@dataclass(frozen=True)
class MultiUnion(Doc):
    alternatives_fn: Callable[[], Iterable[Doc]]

    def layout(self, indent: int) -> str:
        return self.best(DEFAULT_WIDTH, 0).layout(indent)

    def fits(self, width: int, current_length: int) -> bool:
        return any(doc.fits(width, current_length) for doc in self.alternatives_fn())

    def best(self, width: int, current_length: int) -> "Doc":
        default_document = None
        for doc in self.alternatives_fn():
            if doc.fits(width, current_length):
                return doc.best(width, current_length)
            default_document = doc
        return default_document.best(width, current_length)

    def flatten(self) -> "Doc":
        return MultiUnion(lambda: (doc.flatten() for doc in self.alternatives_fn()))


@dataclass(frozen=True)
class Nest(Doc):
    indent: int
    doc: Doc

    def layout(self, indent: int) -> str:
        return self.doc.layout(indent + self.indent)

    def fits(self, width: int, current_length: int) -> bool:
        return self.doc.fits(width, current_length)

    def best(self, width: int, current_length: int) -> "Doc":
        return Nest(self.indent, self.doc.best(width, current_length + self.indent))

    def flatten(self) -> "Doc":
        return Nest(self.indent, self.doc.flatten())


def nil() -> Doc:
    return Nil()


def text(value: str) -> Doc:
    return Text(value) if value != "" else nil()


def line() -> Doc:
    return Line()


def soft_line() -> Doc:
    return SoftLine()


def hard_line() -> Doc:
    return HardLine()


def concat(docs: list[Doc]) -> Doc:
    filtered_docs = [doc for doc in docs if not isinstance(doc, Nil)]

    if not filtered_docs:
        return nil()

    result = filtered_docs[0]
    for doc in filtered_docs[1:]:
        result += doc

    return result


def nest(indent: int, doc: Doc) -> Doc:
    return Nest(indent, doc)


def group(doc: Doc) -> Doc:
    return MultiUnion(lambda: iter([doc.flatten(), doc]))


def parens(doc: Doc, needs_spaces: bool = False) -> Doc:
    line_func = line if needs_spaces else soft_line
    return group(concat([text("("), nest(DEFAULT_TAB_SIZE, concat([line_func(), doc])), line_func(), text(")")]))


def insert_between(separator: Doc, docs: list[Doc]) -> Doc:
    if not docs:
        return nil()

    docs_with_separator = docs[0]
    for doc in docs[1:]:
        docs_with_separator = concat([docs_with_separator, separator, doc])

    return docs_with_separator
