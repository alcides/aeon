from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum, IntEnum

from aeon.sugar.program import (
    SLiteral,
    SVar,
    STerm,
    SAnnotation,
    SApplication,
    SAbstraction,
    SLet,
    SRec,
    SIf,
    STypeAbstraction,
    STypeApplication,
    SHole,
)
from aeon.sugar.stypes import STypeConstructor, STypePolymorphism, SAbstractionType, SRefinedType, STypeVar, SType
from aeon.utils.name import Name

DEFAULT_NEW_LINE_CHAR = "\n"
DEFAULT_SPACE_CHAR = " "
DEFAULT_WIDTH = 80
DEFAULT_TAB_SIZE = 4


class Associativity(Enum):
    LEFT = "left"
    RIGHT = "right"
    NONE = "none"


class Side(Enum):
    LEFT = "left"
    RIGHT = "right"
    NONE = "none"


class Operation(Enum):
    POLYMORPHISM = "Polymorphism"
    LET = "Let"
    IF = "If"
    ARROW = "Arrow"
    LAMBDA = "Lambda"
    REFINED_TYPE = "RefinedType"
    ANNOTATION = "Annotation"
    TYPE_CONSTRUCTOR = "TypeConstructor"
    APPLICATION = "Application"
    TYPE_APPLICATION = "TypeApplication"
    LITERAL = "Literal"


def get_operation_precedence(operation: Operation) -> int:
    precedence_map = {
        Operation.POLYMORPHISM: 1,
        Operation.LET: 2,
        Operation.IF: 2,
        Operation.ARROW: 3,
        Operation.LAMBDA: 4,
        Operation.REFINED_TYPE: 5,
        Operation.ANNOTATION: 6,
        Operation.TYPE_CONSTRUCTOR: 7,
        Operation.APPLICATION: 8,
        Operation.TYPE_APPLICATION: 9,
        Operation.LITERAL: 10,
    }
    return precedence_map[operation]


def get_operation_associativity(operation: Operation) -> Associativity:
    match operation:
        case Operation.LAMBDA, Operation.ARROW:
            return Associativity.RIGHT
        case Operation.APPLICATION, Operation.TYPE_APPLICATION:
            return Associativity.LEFT
        case _:
            return Associativity.NONE


def get_sterm_operation(sterm: STerm) -> Operation:
    match sterm:
        case SLet():
            return Operation.LET
        case SIf():
            return Operation.IF
        case SAbstraction():
            return Operation.LAMBDA
        case SApplication():
            return Operation.APPLICATION
        case SAnnotation():
            return Operation.ANNOTATION
        case SRec():
            return Operation.LET
        case STypeAbstraction():
            return Operation.POLYMORPHISM
        case STypeApplication():
            return Operation.TYPE_APPLICATION
        case SLiteral() | SVar() | SHole():
            return Operation.LITERAL
        case _:
            return Operation.LITERAL


def get_stype_operation(stype: SType) -> Operation:
    match stype:
        case STypeVar():
            return Operation.LITERAL
        case SRefinedType():
            return Operation.REFINED_TYPE
        case SAbstractionType():
            return Operation.ARROW
        case STypePolymorphism():
            return Operation.POLYMORPHISM
        case STypeConstructor():
            return Operation.TYPE_CONSTRUCTOR
        case _:
            return Operation.LITERAL


class Precedence(IntEnum):
    POLYMORPHISM = 1
    LET = 2
    IF = 2
    ARROW = 3
    LAMBDA = 4
    REFINED_TYPE = 5
    ANNOTATION = 6
    TYPE_CONSTRUCTOR = 7
    APPLICATION = 8
    TYPE_APPLICATION = 9
    LITERAL = 10


@dataclass(frozen=True)
class ParenthesisContext:
    parent_precedence: Precedence
    child_side: Side


# "a -> b"
# "a : b -> c"
# "∀a:b -> c"
# "let x in y = z"
# "if x then y else z -> c"
# \x -> \y -> z
# (\x -> \y) -> z
# "let rec x : Int -> Int = y in z"


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


@dataclass(frozen=True)
class Nil(Doc):
    def layout(self, _) -> str:
        return ""

    def fits(self, *_):
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

    def fits(self, *_) -> bool:
        return True

    def best(self, *_) -> "Doc":
        return self

    def flatten(self) -> "Doc":
        return self


@dataclass(frozen=True)
class Concat(Doc):
    left: Doc
    right: Doc

    def layout(self, indent: int) -> str:
        left_layout = self.left.layout(indent)
        right_layout = self.right.layout(indent)
        return left_layout + right_layout

    def fits(self, width: int, current_length: int) -> bool:
        return self.left.fits(width, current_length) and self.right.fits(
            width, current_length + len(self.left.flatten().layout(0))
        )

    def best(self, width: int, current_length: int) -> "Doc":
        left_best = self.left.best(width, current_length)
        right_best = self.right.best(width, current_length + len(left_best.flatten().layout(0)))
        return Concat(left_best, right_best)

    def flatten(self) -> "Doc":
        return Concat(self.left.flatten(), self.right.flatten())


@dataclass(frozen=True)
class MultiUnion(Doc):
    alternatives: tuple[Doc, ...]

    def layout(self, indent: int) -> str:
        return self.best(DEFAULT_WIDTH, indent).layout(indent)

    def fits(self, width: int, current_length: int) -> bool:
        return any(doc.fits(width, current_length) for doc in self.alternatives)

    def best(self, width: int, current_length: int) -> Doc:
        for doc in self.alternatives:
            if doc.fits(width, current_length):
                return doc
        denser_alternative = self.alternatives[-1]
        return denser_alternative

    def flatten(self):
        return self.alternatives[0].flatten()


@dataclass(frozen=True)
class Nest(Doc):
    indent: int
    doc: Doc

    def layout(self, indent: int) -> str:
        return self.doc.layout(indent + self.indent)

    def fits(self, width: int, current_length: int) -> bool:
        doc_layout = self.doc.layout(self.indent)
        lines = doc_layout.split(DEFAULT_NEW_LINE_CHAR)
        return all(len(line) <= width for line in lines)

    def best(self, width: int, current_length: int) -> "Doc":
        best_doc = self.doc.best(width, current_length)
        return Nest(self.indent, best_doc)

    def flatten(self) -> "Doc":
        return self.doc.flatten()


def nil() -> Doc:
    return Nil()


def text(value: str) -> Doc:
    if value == "":
        return nil()
    return Text(value)


def line() -> Doc:
    return Line()


def softline() -> Doc:
    return MultiUnion((text(" "), line()))


def concat(docs: list[Doc]) -> Doc:
    filtered_docs = [doc for doc in docs if not isinstance(doc, Nil)]

    if not filtered_docs:
        return text("")

    result = filtered_docs[0]
    for doc in filtered_docs[1:]:
        result = Concat(result, doc)

    return result


def nest(indent: int, doc: Doc) -> Doc:
    return Nest(indent, doc)


def group(doc: Doc) -> Doc:
    return MultiUnion((doc.flatten(), doc))


def parens(doc: Doc) -> Doc:
    return concat([text("("), doc, text(")")])

def indented(indent: int, doc: Doc) -> Doc:
    return nest(indent, concat([line(), doc]))

def needs_parens(child_operation: Operation, parenthesis_context: ParenthesisContext):
    child_precedence = get_operation_precedence(child_operation)
    parent_precedence = parenthesis_context.parent_precedence
    child_side = parenthesis_context.child_side
    child_associativity = get_operation_associativity(child_operation)

    return needs_parens_aux(child_associativity, child_precedence, child_side, parent_precedence)


def needs_parens_aux(child_associativity, child_precedence, child_side, parent_precedence):
    if child_precedence < parent_precedence:
        return True
    if child_precedence > parent_precedence:
        return False
    if child_associativity == Associativity.NONE:
        return False
    if child_associativity == Associativity.LEFT and child_side == Side.RIGHT:
        return True
    if child_associativity == Associativity.RIGHT and child_side == Side.LEFT:
        return True
    return False


def add_parens_if_needed(doc: Doc, child_operation: Operation, parenthesis_context: ParenthesisContext) -> Doc:
    return parens(doc) if needs_parens(child_operation, parenthesis_context) else doc


@dataclass(frozen=True)
class TypePrettyResult:
    doc: Doc
    operation: Operation


def pretty_stype_with_parens(stype: SType, parent_ctx: ParenthesisContext) -> Doc:
    child_pretty = stype_pretty(stype, parent_ctx)
    child_op = get_stype_operation(stype)
    return add_parens_if_needed(child_pretty, child_op, parent_ctx)


def pretty_sterm_with_parens(sterm: STerm, parent_ctx: ParenthesisContext) -> Doc:
    child_pretty = sterm_pretty(sterm, parent_ctx)
    child_op = get_sterm_operation(sterm)
    return add_parens_if_needed(child_pretty, child_op, parent_ctx)


def stype_pretty(stype: SType, context: ParenthesisContext = None) -> Doc:
    if context is None:
        context = ParenthesisContext(parent_precedence=Precedence.LITERAL, child_side=Side.NONE)

    match stype:
        case STypeVar(name=name):
            return text(f"{name.pretty()}")

        case SRefinedType(name=name, type=type_, refinement=refinement):
            pretty_name = text(name.pretty())

            type_doc = pretty_stype_with_parens(type_, ParenthesisContext(Precedence.REFINED_TYPE, Side.RIGHT))
            refinement_doc = pretty_sterm_with_parens(
                refinement, ParenthesisContext(Precedence.REFINED_TYPE, Side.RIGHT)
            )

            var_type_pair = concat([pretty_name, text(" : "), type_doc])

            flat = concat(
                [
                    text("{ "),
                    var_type_pair,
                    text(" | "),
                    refinement_doc,
                    text(" }"),
                ],
            )

            extended = concat(
                [
                    text("{ "),
                    var_type_pair,
                    line(),
                    text("| "),
                    refinement_doc,
                    line(),
                    text("}"),
                ],
            )

            return MultiUnion((flat, extended))

        case SAbstractionType(var_name=var_name, var_type=var_type, type=type):
            pretty_var_name = text(var_name.pretty())
            var_type_doc = pretty_stype_with_parens(var_type, ParenthesisContext(Precedence.ANNOTATION, Side.RIGHT))
            left_doc = concat([pretty_var_name, text(" : "), var_type_doc])

            right_doc = pretty_stype_with_parens(type, ParenthesisContext(Precedence.ARROW, Side.RIGHT))

            flat = concat([left_doc, text(" -> "), right_doc])
            extended = concat([left_doc, text(" -> ("), indented(DEFAULT_TAB_SIZE,right_doc), line(), text(")")])
            return MultiUnion((flat, extended))

        case STypePolymorphism(name=name, kind=kind, body=body):
            pretty_name = text(name.pretty())
            pretty_kind = text(str(kind))  # should be changed to skind pretty in the future

            pretty_body = pretty_stype_with_parens(body, ParenthesisContext(Precedence.POLYMORPHISM, Side.RIGHT))

            left = concat([text("∀"), pretty_name, text(" : "), pretty_kind])
            flat = concat([left, text(" . "), pretty_body])
            # extended = ...
            return flat
        case STypeConstructor(name=name, args=args):
            pretty_name = text(name.pretty())
            if not args:
                return pretty_name

            pretty_args = [
                pretty_stype_with_parens(arg, ParenthesisContext(Precedence.TYPE_CONSTRUCTOR, Side.RIGHT))
                for arg in args
            ]

            if len(args) == 1:
                return concat([pretty_name, text(" "), pretty_args[0]])
            else:
                pretty_arg_doc = insert_between(text(", "), pretty_args)
                return concat([pretty_name, text(" ("), pretty_arg_doc, text(")")])
        case _:
            return text(str(stype))


def sterm_pretty(sterm: STerm, context: ParenthesisContext = None) -> Doc:
    if context is None:
        context = ParenthesisContext(parent_precedence=Precedence.LITERAL, child_side=Side.NONE)

    match sterm:
        case SLiteral(value=value, type=type):
            if type == STypeConstructor(Name("String", 0)):
                return text(f'"{value}"')
            return text(str(value))
        case SVar(name=name):
            return text(name.pretty())
        case SHole(name=name):
            return text("?" + name.pretty())
        case SAnnotation(expr=expr, type=type):
            expr_doc = pretty_sterm_with_parens(expr, ParenthesisContext(Precedence.ANNOTATION, Side.LEFT))
            type_doc = stype_pretty(type, ParenthesisContext(Precedence.ANNOTATION, Side.RIGHT))
            return concat([expr_doc, text(" : "), type_doc])

        case SIf(cond=cond, then=then, otherwise=otherwise):
            pretty_cond = pretty_sterm_with_parens(cond, ParenthesisContext(Precedence.IF, Side.NONE))
            pretty_then = pretty_sterm_with_parens(then, ParenthesisContext(Precedence.IF, Side.NONE))
            pretty_otherwise = pretty_sterm_with_parens(otherwise, ParenthesisContext(Precedence.IF, Side.NONE))

            inline = concat([text("if "), pretty_cond, text(" then "), pretty_then, text(" else "), pretty_otherwise])
            first_extended = concat(
                [text("if "), pretty_cond, text(" then "), pretty_then, line(), text("else "), pretty_otherwise]
            )
            second_extended = concat(
                [text("if "), pretty_cond, line(), text("then "), pretty_then, line(), text("else "), pretty_otherwise]
            )
            return MultiUnion((inline, first_extended, second_extended))
        case SApplication(fun=fun, arg=arg):
            pretty_fun = pretty_sterm_with_parens(fun, ParenthesisContext(Precedence.APPLICATION, Side.LEFT))
            pretty_arg = pretty_sterm_with_parens(arg, ParenthesisContext(Precedence.APPLICATION, Side.RIGHT))

            flat = concat([pretty_fun, text(DEFAULT_SPACE_CHAR), pretty_arg])
            # extended = ...
            return flat

        case SAbstraction(var_name=var_name, body=body):
            pretty_var_name = text(var_name.pretty())
            pretty_body = pretty_sterm_with_parens(body, ParenthesisContext(Precedence.ARROW, Side.RIGHT))
            left_doc = concat([text("\\"), pretty_var_name])
            right_doc = pretty_body

            flat = concat([left_doc, text(" -> "), right_doc])
            extended = concat([left_doc, text(" -> ("), indented(DEFAULT_TAB_SIZE,right_doc), line(), text(")")])

            return MultiUnion((flat, extended))

        case SLet(var_name=var_name, var_value=var_value, body=body):
            pretty_var_name = text(var_name.pretty())
            pretty_var_value = pretty_sterm_with_parens(var_value, ParenthesisContext(Precedence.LET, Side.NONE))
            pretty_body = pretty_sterm_with_parens(body, ParenthesisContext(Precedence.LET, Side.NONE))

            binding = concat([pretty_var_name, text(" = "), pretty_var_value])

            flat = concat([text("let "), binding, text(" in "), pretty_body])
            extended = concat([text("let "), binding, line(), text("in "), pretty_body])

            return MultiUnion((flat, extended))

        case SRec(var_name=var_name, var_type=var_type, var_value=var_value, body=body):
            pretty_var_name = text(var_name.pretty())
            pretty_var_type = pretty_stype_with_parens(var_type, ParenthesisContext(Precedence.ANNOTATION, Side.RIGHT))
            pretty_var_value = pretty_sterm_with_parens(var_value, ParenthesisContext(Precedence.LET, Side.NONE))
            pretty_body = pretty_sterm_with_parens(body, ParenthesisContext(Precedence.LET, Side.NONE))

            pretty_type_def = concat([pretty_var_name, text(" : "), pretty_var_type])
            pretty_binding = concat([pretty_type_def, text(" = "), pretty_var_value])

            flat = concat([text("let "), pretty_binding, text(" in "), pretty_body])
            extended = concat([text("let "), pretty_binding, line(), text("in "), pretty_body])

            return MultiUnion((flat, extended))

        case STypeAbstraction(name=name, kind=kind, body=body):
            pretty_name = text(name.pretty())
            pretty_kind = text(str(kind))  # should be changed to skind pretty in the future
            pretty_body = pretty_sterm_with_parens(body, ParenthesisContext(Precedence.APPLICATION, Side.RIGHT))

            pretty_kind_def = concat([pretty_name, text(" : "), pretty_kind])
            pretty_binding = concat([pretty_kind_def, text("."), pretty_body])
            flat = concat([text("ƛ"), pretty_binding])
            # extended...
            return flat
        case STypeApplication(body=body, type=type):
            pretty_body = pretty_sterm_with_parens(body, ParenthesisContext(Precedence.TYPE_APPLICATION, Side.LEFT))
            pretty_type = pretty_stype_with_parens(type, ParenthesisContext(Precedence.TYPE_APPLICATION, Side.RIGHT))

            pretty_type_app = concat([text("["), pretty_type, text("]")])

            flat = concat([pretty_body, pretty_type_app])
            # extended...
            return flat
        case _:
            return text(str(sterm))


def insert_between(separator: Doc, docs: list[Doc]) -> Doc:
    if not docs:
        return nil()
    result = docs[0]
    for doc in docs[1:]:
        result = concat([result, separator, doc])
    return result


# TODO
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
    return sterm_pretty(remove_anf(term), None).best(width, 0).layout(0)
