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
    return MultiUnion((doc.flatten(), doc))


def pretty_var_type_pair(name_doc: Doc, type_doc: Doc) -> Doc:
    return concat([name_doc, text(" : "), type_doc], ANNOTATION_PRECEDENCE)


def stype_pretty(stype: SType) -> Doc:
    match stype:
        case STypeVar(name=name):
            return text(f"{name.pretty()}")

        case SRefinedType(name=name, type=type_, refinement=refinement):
            pretty_name = text(name.pretty())
            pretty_type = stype_pretty(type_)
            pretty_refinement = sterm_pretty(refinement)

            flat = concat([
                text("{ "),
                pretty_var_type_pair(pretty_name, pretty_type),
                text(" | "),
                pretty_refinement,
                text(" }"),
            ], REFINED_TYPE_PRECEDENCE)

            extended = concat([
                text("{ "),
                pretty_var_type_pair(pretty_name, pretty_type),
                line(),
                text("| "),
                pretty_refinement,
                line(),
                text("}"),
            ], REFINED_TYPE_PRECEDENCE)

            return MultiUnion((flat, extended))

        case SAbstractionType(var_name=var_name, var_type=var_type, type=type):
            pretty_var_name = text(var_name.pretty())
            pretty_var_type = stype_pretty(var_type)
            left = pretty_var_type_pair(pretty_var_name, pretty_var_type)
            right = stype_pretty(type)

            flat = concat([left, text(" -> "), right], ARROW_PRECEDENCE, Assoc.RIGHT)
            extended = concat([left, text(" -> ("), line(), nest(2, right), line(), text(")")], ARROW_PRECEDENCE,
                              Assoc.NONE)
            return MultiUnion((flat, extended))

        case STypePolymorphism(name=name, kind=kind, body=body):
            pretty_name = text(name.pretty())
            pretty_kind = text(str(kind))  # should be changed to skind pretty in the future
            pretty_body = stype_pretty(body)
            left = concat([text("∀ "), pretty_var_type_pair(pretty_name, pretty_kind)], POLYMORPHISM_PRECEDENCE)
            right = pretty_body

            flat = concat([left, text(" . "), right], POLYMORPHISM_PRECEDENCE, Assoc.RIGHT)
            # extended = ...
            return flat
        case STypeConstructor(name=name, args=args):
            pretty_name = text(name.pretty())
            if len(args) == 0:
                return pretty_name

            pretty_args = [stype_pretty(arg) for arg in args]

            if len(args) == 1:
                return concat([pretty_name, text(DEFAULT_SPACE_CHAR), pretty_args[0]], TYPE_CONSTRUCTOR_PRECEDENCE, Assoc.LEFT)
            else:
                pretty_arg_doc = insert_between(text(", "), pretty_args)
                return concat([pretty_name, text(" ("), pretty_arg_doc, text(")")], TYPE_CONSTRUCTOR_PRECEDENCE)
        case _:
            return text(str(stype))


def sterm_pretty(sterm: STerm) -> Doc:
    match sterm:
        case SLiteral(value=value, type=type):
            if type == STypeConstructor(Name("String", 0)):
                return text(f'"{value}"')
            return text(str(value))
        case SVar(name=name):
            return text(name.pretty())
        case SAnnotation(expr=expr, type=type):
            pretty_expr = sterm_pretty(expr)
            pretty_type = stype_pretty(type)
            flat = pretty_var_type_pair(pretty_expr, pretty_type)
            return flat
        case SHole(name=name):
            return text("?" + name.pretty())
        case SIf(cond=cond, then=then, otherwise=otherwise):
            pretty_cond = sterm_pretty(cond)
            pretty_then = sterm_pretty(then)
            pretty_otherwise = sterm_pretty(otherwise)

            inline = concat([text("if "), pretty_cond, text(" then "), pretty_then, text(" else "), pretty_otherwise],
                            IF_PRECEDENCE)
            first_extended = concat(
                [text("if "), pretty_cond, text(" then "), pretty_then, line(), text("else "), pretty_otherwise],
                IF_PRECEDENCE)
            second_extended = concat(
                [text("if "), pretty_cond, line(), text("then "), pretty_then, line(), text("else "), pretty_otherwise],
                IF_PRECEDENCE)
            return MultiUnion((inline, first_extended, second_extended))
        case SApplication(fun=fun, arg=arg):
            pretty_fun = sterm_pretty(fun)
            pretty_arg = sterm_pretty(arg)

            flat = concat([pretty_fun, text(DEFAULT_SPACE_CHAR), pretty_arg], APPLICATION_PRECEDENCE, Assoc.LEFT)
            # extended = ...
            return flat

        case SAbstraction(var_name=var_name, body=body):
            pretty_var_name = text(var_name.pretty())
            pretty_body = sterm_pretty(body)
            left = concat([text("\\"), pretty_var_name], POLYMORPHISM_PRECEDENCE)
            right = pretty_body

            flat = concat([left, text(" -> "), right], LAMBDA_PRECEDENCE, Assoc.RIGHT)
            extended = concat([left, text(" -> ("), line(), nest(DEFAULT_TAB_SIZE, right), line(), text(')')],
                              LAMBDA_PRECEDENCE)

            return MultiUnion((flat, extended))

        case SLet(var_name=var_name, var_value=var_value, body=body):
            pretty_var_name = text(var_name.pretty())
            pretty_var_value = sterm_pretty(var_value)
            pretty_body = sterm_pretty(body)

            binding = concat([pretty_var_name, text(" = "), pretty_var_value], LET_PRECEDENCE, Assoc.RIGHT)

            flat = concat([text("let "), binding, text(" in "), pretty_body], LAMBDA_PRECEDENCE)
            extended = concat([text("let "), binding, line(), text("in "), pretty_body], LAMBDA_PRECEDENCE)

            return MultiUnion((flat, extended))

        case SRec(var_name=var_name, var_type=var_type, var_value=var_value, body=body):
            pretty_var_name = text(var_name.pretty())
            pretty_var_type = stype_pretty(var_type)
            pretty_var_value = sterm_pretty(var_value)
            pretty_body = sterm_pretty(body)

            pretty_type_def = pretty_var_type_pair(pretty_var_name, pretty_var_type)
            pretty_binding = concat([pretty_type_def, text(" = "), pretty_var_value], LET_PRECEDENCE, Assoc.RIGHT)

            flat = concat([text("let "), pretty_binding, text(" in "), pretty_body], LET_PRECEDENCE)
            extended = concat([text("let "), pretty_binding, line(),text("in "), pretty_body], LET_PRECEDENCE)

            return MultiUnion((flat, extended))

        case STypeAbstraction(name=name, kind=kind, body=body):
            pretty_name = text(name.pretty())
            pretty_kind = text(str(kind)) # should be changed to skind pretty in the future
            pretty_body = sterm_pretty(body)

            pretty_kind_def = pretty_var_type_pair(pretty_name, pretty_kind)
            pretty_binding = concat([pretty_kind_def,text("."),pretty_body], ARROW_PRECEDENCE, Assoc.RIGHT)
            flat = concat([text("ƛ"),pretty_binding], ARROW_PRECEDENCE)
            #extended...
            return flat
        case STypeApplication(body=body, type=type):
            pretty_body = sterm_pretty(body)
            pretty_type = stype_pretty(type)
            pretty_type_app = concat([text("["),pretty_type,text("]")],TYPE_APPLICATION_PRECEDENCE)

            flat = concat([pretty_body,nil(),pretty_type_app], TYPE_APPLICATION_PRECEDENCE)
            #extended...
            return flat
        case _:
            return text(str(sterm))

def insert_between(separator: Doc, docs: list[Doc]) -> Doc:
    if not docs:
        return nil()
    result = docs[0]
    for doc in docs[1:]:
        result = concat([result, separator, doc], LITERAL_PRECEDENCE, Assoc.NONE)
    return result

#TODO
def remove_anf(term: STerm) -> STerm:
    match term:
        case SLet(var_name=var_name, var_value=var_value, body=SVar(name=body_name)) if var_name == body_name:
            return remove_anf(var_value)
        case SLet(var_name=var_name, var_value=var_value, body=body):
            return SLet(var_name, remove_anf(var_value), remove_anf(body))
        case SAbstraction(var_name=var_name, body=body):
            return SAbstraction(var_name, remove_anf(body))
        case SApplication(fun=fun, arg=arg):
            return SApplication(remove_anf(fun), remove_anf(arg))
        case SRec(var_name=var_name, var_type=var_type, var_value=var_value, body=body):
            return SRec(var_name, var_type, remove_anf(var_value), remove_anf(body))
        case SIf(cond=cond, then=then, otherwise=otherwise):
            return SIf(remove_anf(cond), remove_anf(then), remove_anf(otherwise))
        case _:
            return term


def pretty_print(term: STerm, width: int = DEFAULT_WIDTH) -> str:
    return (
        sterm_pretty(remove_anf(term))
        .best(width, 0)
        .layout(LayoutContext(indent=0, position=Position.NONE, parent_precedence=0))
    )
