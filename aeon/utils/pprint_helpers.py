from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum, IntEnum
from functools import reduce
from typing import Callable, List

from aeon.sugar.ast_helpers import true, false
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

AEON_INFIX_OPERATORS = {
    "%",
    "/",
    "*",
    "-",
    "+",
    "%.",
    "/.",
    "*.",
    "-.",
    "+.",
    ">=",
    ">",
    "<=",
    "<",
    "!=",
    "==",
    "&&",
    "||",
}


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
    ANNOTATION = 3
    ARROW = 4
    LAMBDA = 5
    REFINED_TYPE = 6
    TYPE_CONSTRUCTOR = 7
    APPLICATION = 8
    TYPE_APPLICATION = 9
    LITERAL = 10


def get_operation_precedence(operation: Operation) -> Precedence:
    precedence_map = {
        Operation.POLYMORPHISM: Precedence.POLYMORPHISM,
        Operation.LET: Precedence.LET,
        Operation.IF: Precedence.IF,
        Operation.ARROW: Precedence.ARROW,
        Operation.LAMBDA: Precedence.LAMBDA,
        Operation.REFINED_TYPE: Precedence.REFINED_TYPE,
        Operation.ANNOTATION: Precedence.ANNOTATION,
        Operation.TYPE_CONSTRUCTOR: Precedence.TYPE_CONSTRUCTOR,
        Operation.APPLICATION: Precedence.APPLICATION,
        Operation.TYPE_APPLICATION: Precedence.TYPE_APPLICATION,
        Operation.LITERAL: Precedence.LITERAL,
    }
    return precedence_map[operation]


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

    result = docs[0]
    for doc in docs[1:]:
        result = concat([result, separator, doc])

    return result


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
    # quick and dirty fix for the parenthesis around fun application e.g. -> f (f y)
    if child_precedence == parent_precedence == Precedence.APPLICATION and child_side == Side.RIGHT:
        return True
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
    child_op = get_stype_operation(stype)
    child_pretty = stype_pretty(stype, ParenthesisContext(get_operation_precedence(child_op), Side.NONE))
    return add_parens_if_needed(child_pretty, child_op, parent_ctx)


def pretty_sterm_with_parens(sterm: STerm, parent_ctx: ParenthesisContext) -> Doc:
    child_op = get_sterm_operation(sterm)
    child_pretty = sterm_pretty(sterm, ParenthesisContext(get_operation_precedence(child_op), Side.NONE))
    return add_parens_if_needed(child_pretty, child_op, parent_ctx)


def format_infix_application(left: STerm, right: STerm, op_name: Name, depth: int):
    pretty_left = pretty_sterm_with_parens(left, ParenthesisContext(Precedence.APPLICATION, Side.LEFT), depth + 1)
    pretty_right = pretty_sterm_with_parens(right, ParenthesisContext(Precedence.APPLICATION, Side.RIGHT), depth + 1)
    return group(concat([pretty_left, line(), text(op_name.pretty()), line(), pretty_right]))


def pretty_print_function_definition(pretty_var_name, named_vars, final_type):
    first_var_name, first_var_type = named_vars[0]
    first_arg_str = parens(concat([text(first_var_name.pretty()), text(" : "), stype_pretty(first_var_type)]))
    header = concat([text("def "), pretty_var_name, text(" "), first_arg_str])

    alignment = len("def ") + len(pretty_var_name.layout(0)) + 1

    for var_name, var_type in named_vars[1:]:
        pretty_arg = concat(
            [
                line(),
                text(" " * alignment),
                parens(concat([text(var_name.pretty()), text(" : "), stype_pretty(var_type)])),
            ]
        )
        header = concat([header, pretty_arg])

    header = concat(
        [
            header,
            nest(alignment, concat([line(), text(": "), stype_pretty(final_type)])),
        ]
    )
    return header, alignment


def unwrap_abstraction_types(stype: SType):
    named_vars = []
    curr = stype
    while True:
        match curr:
            case SAbstractionType(var_name=_var_name, var_type=_var_type, type=next_type):
                named_vars.append((_var_name, _var_type))
                curr = next_type
            case other:
                return named_vars, other


def strip_matching_abstractions(value: STerm, named_vars):
    for var_name, _ in named_vars:
        match value:
            case SAbstraction(var_name=vn, body=body) if vn.name == var_name.name:
                value = body
            case _:
                break
    return value


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
            left_doc = add_parens_if_needed(
                left_doc, Operation.ANNOTATION, ParenthesisContext(Precedence.ARROW, Side.LEFT)
            )

            right_doc = pretty_stype_with_parens(type, ParenthesisContext(Precedence.ARROW, Side.RIGHT))

            flat = concat([left_doc, text(" -> "), right_doc])
            extended = concat([left_doc, text(" -> ("), indented(DEFAULT_TAB_SIZE, right_doc), line(), text(")")])
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
            extended = concat([left_doc, text(" -> ("), indented(DEFAULT_TAB_SIZE, right_doc), line(), text(")")])

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
            pretty_body = sterm_pretty(body, ParenthesisContext(Precedence.APPLICATION, Side.LEFT))
            pretty_type = stype_pretty(type, ParenthesisContext(Precedence.APPLICATION, Side.RIGHT))

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


def normalize_term(term: STerm, context: dict[Name, STerm] = None, seen: set[Name] = None) -> STerm:
    if context is None:
        context = {}
    if seen is None:  # seen is used as a fix to infinite recursion
        seen = set()

    match term:
        case SLiteral(value=value, type=type):
            return SLiteral(value=value, type=type)
        case SVar(name=name):
            if name in seen or name not in context:
                return SVar(name=name)
            simplified_term = context[name]
            new_seen = seen.copy()
            new_seen.add(name)
            return normalize_term(simplified_term, context, new_seen)
        case SHole(name=name):
            return SHole(name=name)
        case SAnnotation(expr=expr, type=type):
            simplified_expr = normalize_term(expr, context, seen)
            return SAnnotation(expr=simplified_expr, type=type)
        case SIf(cond=cond, then=then, otherwise=otherwise):
            simplified_cond = normalize_term(cond, context, seen)
            if simplified_cond == true:
                simplified_cond = normalize_term(cond, context, seen)
                return simplified_cond
            elif simplified_cond == false:
                simplified_otherwise = normalize_term(otherwise, context, seen)
                return normalize_term(simplified_otherwise, context, seen)
            else:
                simplified_then = normalize_term(then, context, seen)
                simplified_otherwise = normalize_term(otherwise, context, seen)
                return SIf(cond=simplified_cond, then=simplified_then, otherwise=simplified_otherwise)
        case SApplication(fun=fun, arg=arg):
            simplified_fun = normalize_term(fun, context, seen)
            simplified_arg = normalize_term(arg, context, seen)

            if isinstance(simplified_fun, SAbstraction):
                new_context = context.copy()
                new_context[simplified_fun.var_name] = simplified_arg
                return normalize_term(simplified_fun.body, new_context, seen)
            else:
                return SApplication(fun=simplified_fun, arg=simplified_arg)
        case SAbstraction(var_name=var_name, body=body):
            simplified_body = normalize_term(body, context, seen)
            return SAbstraction(var_name=var_name, body=simplified_body)
        case SLet(var_name=var_name, var_value=var_value, body=body):
            if var_name.pretty() == "anf":
                context_copy = context.copy()
                context_copy[var_name] = normalize_term(var_value, context, seen)
                simplified_body = normalize_term(body, context_copy, seen)
                return simplified_body
            return SLet(
                var_name=var_name,
                var_value=normalize_term(var_value, context, seen),
                body=normalize_term(body, context, seen),
            )
        case SRec(var_name=var_name, var_type=var_type, var_value=var_value, body=body):
            if var_name.pretty() == "anf":
                context_copy = context.copy()
                context_copy[var_name] = normalize_term(var_value, context, seen)
                simplified_body = normalize_term(body, context_copy, seen)
                return simplified_body
            return SRec(
                var_name=var_name,
                var_type=var_type,
                var_value=normalize_term(var_value, context, seen),
                body=normalize_term(body, context, seen),
            )
        case STypeAbstraction(name=name, kind=kind, body=body):
            simplified_body = normalize_term(body, context, seen)
            return STypeAbstraction(name=name, kind=kind, body=simplified_body)
        case _:
            return term


def rename_unused_variables(term: STerm):
    # TODO
    return term


def pretty_print(term: STerm) -> str:
    def apply_func(acc: STerm, func: Callable[[STerm], STerm]) -> STerm:
        return func(acc)

    functions: List[Callable[[STerm], STerm]] = [normalize_term, rename_unused_variables]

    simplified_term = reduce(apply_func, functions, term)
    return str(sterm_pretty(simplified_term))
