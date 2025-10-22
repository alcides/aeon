from dataclasses import dataclass
from enum import IntEnum, Enum, auto
from functools import reduce
from typing import Callable, List, Tuple

from aeon.sugar.ast_helpers import true, false
from aeon.sugar.program import (
    SLet,
    SIf,
    SAbstraction,
    SApplication,
    SAnnotation,
    SRec,
    STypeAbstraction,
    STypeApplication,
    SLiteral,
    SVar,
    SHole,
    STerm,
    Node,
    ImportAe,
    TypeDecl,
    Decorator,
    InductiveDecl,
    Definition,
    Program,
)
from aeon.sugar.stypes import SType, STypeVar, SRefinedType, SAbstractionType, STypePolymorphism, STypeConstructor
from aeon.utils.name import Name
from aeon.utils.pprint_helpers import (
    Doc,
    parens,
    group,
    concat,
    line,
    text,
    nest,
    DEFAULT_WIDTH,
    soft_line,
    DEFAULT_TAB_SIZE,
    insert_between,
    nil,
    hard_line,
)


class Operation(Enum):
    INFIX_MULTIPLICATIVE = auto()
    INFIX_ADDITIVE = auto()
    INFIX_RELATIONAL = auto()
    INFIX_AND = auto()
    INFIX_OR = auto()
    POLYMORPHISM = auto()
    LET = auto()
    IF = auto()
    ARROW = auto()
    LAMBDA = auto()
    REFINED_TYPE = auto()
    ANNOTATION = auto()
    TYPE_CONSTRUCTOR = auto()
    APPLICATION = auto()
    TYPE_APPLICATION = auto()
    LITERAL = auto()


class Precedence(IntEnum):
    POLYMORPHISM = 1
    LET = 2
    IF = 2
    ANNOTATION = 3
    ARROW = 4
    LAMBDA = 5
    REFINED_TYPE = 6
    TYPE_CONSTRUCTOR = 7
    INFIX_OR = 8
    INFIX_AND = 9
    INFIX_RELATIONAL = 10
    INFIX_ADDITIVE = 11
    INFIX_MULTIPLICATIVE = 12
    APPLICATION = 13
    TYPE_APPLICATION = 14
    LITERAL = 15


class Associativity(Enum):
    LEFT = auto()
    RIGHT = auto()
    NONE = auto()


@dataclass(frozen=True)
class OperationInfo:
    precedence: Precedence
    associativity: Associativity


OPERATION_INFO = {
    Operation.POLYMORPHISM: OperationInfo(Precedence.POLYMORPHISM, Associativity.NONE),
    Operation.LET: OperationInfo(Precedence.LET, Associativity.NONE),
    Operation.IF: OperationInfo(Precedence.IF, Associativity.NONE),
    Operation.ANNOTATION: OperationInfo(Precedence.ANNOTATION, Associativity.NONE),
    Operation.ARROW: OperationInfo(Precedence.ARROW, Associativity.RIGHT),
    Operation.LAMBDA: OperationInfo(Precedence.LAMBDA, Associativity.RIGHT),
    Operation.REFINED_TYPE: OperationInfo(Precedence.REFINED_TYPE, Associativity.NONE),
    Operation.TYPE_CONSTRUCTOR: OperationInfo(Precedence.TYPE_CONSTRUCTOR, Associativity.NONE),
    Operation.INFIX_MULTIPLICATIVE: OperationInfo(Precedence.INFIX_MULTIPLICATIVE, Associativity.LEFT),
    Operation.INFIX_ADDITIVE: OperationInfo(Precedence.INFIX_ADDITIVE, Associativity.LEFT),
    Operation.INFIX_RELATIONAL: OperationInfo(Precedence.INFIX_RELATIONAL, Associativity.NONE),
    Operation.INFIX_AND: OperationInfo(Precedence.INFIX_AND, Associativity.LEFT),
    Operation.INFIX_OR: OperationInfo(Precedence.INFIX_OR, Associativity.LEFT),
    Operation.APPLICATION: OperationInfo(Precedence.APPLICATION, Associativity.LEFT),
    Operation.TYPE_APPLICATION: OperationInfo(Precedence.TYPE_APPLICATION, Associativity.LEFT),
    Operation.LITERAL: OperationInfo(Precedence.LITERAL, Associativity.NONE),
}


def get_operation_precedence(operation: Operation) -> Precedence:
    return OPERATION_INFO[operation].precedence


def get_operation_associativity(operation: Operation) -> Associativity:
    return OPERATION_INFO[operation].associativity


INFIX_MULTIPLICATIVE = {"*", "/", "%", "*.", "/.", "%."}
INFIX_ADDITIVE = {"+", "-", "+.", "-."}
INFIX_RELATIONAL = {"<", "<=", ">", ">=", "==", "!="}
INFIX_AND = {"&&"}
INFIX_OR = {"||"}

AEON_INFIX_OPERATORS = INFIX_MULTIPLICATIVE | INFIX_ADDITIVE | INFIX_RELATIONAL | INFIX_AND | INFIX_OR


def get_sterm_operation(sterm: STerm) -> Operation:
    match sterm:
        case SLet():
            return Operation.LET
        case SIf():
            return Operation.IF
        case SAbstraction():
            return Operation.LAMBDA
        case SApplication(fun=SApplication(fun=SVar(name=op_name), arg=_, loc=_), arg=_, loc=_) if (
            op_name.pretty() in AEON_INFIX_OPERATORS
        ):
            return get_infix_op(op_name)
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


def get_infix_op(op_name: Name) -> Operation:
    op = op_name.pretty()
    if op in INFIX_MULTIPLICATIVE:
        return Operation.INFIX_MULTIPLICATIVE
    elif op in INFIX_ADDITIVE:
        return Operation.INFIX_ADDITIVE
    elif op in INFIX_RELATIONAL:
        return Operation.INFIX_RELATIONAL
    elif op in INFIX_AND:
        return Operation.INFIX_AND
    elif op in INFIX_OR:
        return Operation.INFIX_OR
    else:
        return Operation.INFIX_OR


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


class Side(Enum):
    LEFT = "left"
    RIGHT = "right"
    NONE = "none"


@dataclass(frozen=True)
class ParenthesisContext:
    parent_precedence: Precedence
    child_side: Side


def needs_parens(child_operation: Operation, parenthesis_context: ParenthesisContext) -> bool:
    child_precedence = get_operation_precedence(child_operation)
    parent_precedence = parenthesis_context.parent_precedence
    child_side = parenthesis_context.child_side
    child_associativity = get_operation_associativity(child_operation)

    return needs_parens_aux(child_associativity, child_precedence, child_side, parent_precedence)


def needs_parens_aux(
    child_associativity: Associativity, child_precedence: Precedence, child_side: Side, parent_precedence: Precedence
) -> bool:
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


def pretty_stype_with_parens(stype: SType, parenthesis_context: ParenthesisContext) -> Doc:
    child_operation = get_stype_operation(stype)
    child_pretty = stype_pretty(stype, ParenthesisContext(get_operation_precedence(child_operation), Side.NONE))
    return add_parens_if_needed(child_pretty, child_operation, parenthesis_context)


def pretty_sterm_with_parens(sterm: STerm, parenthesis_context: ParenthesisContext, depth: int) -> Doc:
    child_op = get_sterm_operation(sterm)
    child_pretty = sterm_pretty(sterm, ParenthesisContext(get_operation_precedence(child_op), Side.NONE), depth)
    return add_parens_if_needed(child_pretty, child_op, parenthesis_context)


def format_infix_application(left: STerm, right: STerm, op_name: Name, depth: int) -> Doc:
    infix_op = get_infix_op(op_name)
    infix_precedence = get_operation_precedence(infix_op)
    pretty_left = pretty_sterm_with_parens(left, ParenthesisContext(infix_precedence, Side.LEFT), depth + 1)
    pretty_right = pretty_sterm_with_parens(right, ParenthesisContext(infix_precedence, Side.RIGHT), depth + 1)
    return group(concat([pretty_left, line(), text(op_name.pretty()), line(), pretty_right]))


def pretty_param_doc(param_name: Name, param_type: SType) -> Doc:
    match param_type:
        case SRefinedType(name=ref_name, type=ref_type, refinement=refinement):
            if ref_name.pretty() == param_name.pretty():
                return parens(
                    concat(
                        [
                            text(ref_name.pretty()),
                            text(" : "),
                            stype_pretty(ref_type),
                            text(" | "),
                            sterm_pretty(refinement, ParenthesisContext(Precedence.REFINED_TYPE, Side.RIGHT), depth=1),
                        ]
                    )
                )
    return parens(
        concat(
            [
                text(param_name.pretty()),
                text(" : "),
                stype_pretty(param_type),
            ]
        )
    )


def pretty_print_function_definition(
    func_name_doc: Doc, params: List[Tuple[Name, SType]], return_type: SType
) -> Tuple[Doc, int]:
    first_param_name, first_param_type = params[0]
    first_param_doc = pretty_param_doc(first_param_name, first_param_type)
    func_header = concat([text("def "), func_name_doc, text(" "), first_param_doc])

    indent_after_first_param = len("def ") + len(func_name_doc.layout(0)) + 1
    additional_params = nil()
    for param_name, param_type in params[1:]:
        additional_params = concat(
            [
                additional_params,
                line(),
                pretty_param_doc(param_name, param_type),
            ]
        )
    full_func_def = concat(
        [
            func_header,
            nest(indent_after_first_param, concat([additional_params, line(), text(": "), stype_pretty(return_type)])),
        ]
    )
    return full_func_def, indent_after_first_param


def unwrap_abstraction_types(stype: SType) -> Tuple[List[Tuple[Name, SType]], SType]:
    named_vars = []
    curr = stype
    while True:
        match curr:
            case SAbstractionType(var_name=_var_name, var_type=_var_type, type=next_type):
                named_vars.append((_var_name, _var_type))
                curr = next_type
            case other:
                return named_vars, other


def strip_matching_abstractions(abstraction: STerm, arguments: List[Tuple[Name, SType]]) -> STerm:
    stripped_abstraction = abstraction
    for argument_name, _ in arguments:
        match stripped_abstraction:
            case SAbstraction(var_name=_var_name, body=body) if _var_name.name == argument_name.name:
                stripped_abstraction = body
            case _:
                break
    return stripped_abstraction


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
                refinement, ParenthesisContext(Precedence.REFINED_TYPE, Side.RIGHT), 1
            )

            var_type_pair = concat([pretty_name, text(" : "), type_doc])

            return group(
                concat(
                    [
                        text("{"),
                        nest(DEFAULT_WIDTH, concat([soft_line(), var_type_pair, text(" | "), refinement_doc])),
                        soft_line(),
                        text("}"),
                    ]
                )
            )

        case SAbstractionType(var_name=var_name, var_type=var_type, type=_type):
            pretty_var_name = text(var_name.pretty())
            var_type_doc = pretty_stype_with_parens(var_type, ParenthesisContext(Precedence.ANNOTATION, Side.RIGHT))

            left_doc = concat([pretty_var_name, text(" : "), var_type_doc])
            left_doc = add_parens_if_needed(
                left_doc, Operation.ANNOTATION, ParenthesisContext(Precedence.ARROW, Side.LEFT)
            )

            right_doc = pretty_stype_with_parens(_type, ParenthesisContext(Precedence.ARROW, Side.RIGHT))

            return group(concat([left_doc, text(" ->"), line(), right_doc]))

        case STypePolymorphism(name=name, kind=kind, body=body):
            pretty_name = text(name.pretty())
            pretty_kind = text(str(kind))  # should be changed to skind pretty in the future

            pretty_body = pretty_stype_with_parens(body, ParenthesisContext(Precedence.POLYMORPHISM, Side.RIGHT))

            left = concat([text("∀"), pretty_name, text(" : "), pretty_kind])

            return group(concat([left, text(" ."), nest(DEFAULT_TAB_SIZE, concat([line(), pretty_body]))]))

        case STypeConstructor(name=name, args=args):
            pretty_name = text(name.pretty())
            if not args:
                return pretty_name

            pretty_args = [
                pretty_stype_with_parens(arg, ParenthesisContext(Precedence.TYPE_CONSTRUCTOR, Side.RIGHT))
                for arg in args
            ]

            pretty_args_doc = insert_between(text(" "), pretty_args)
            return group(concat([pretty_name, text(" "), pretty_args_doc]))

        case _:
            return text(str(stype))


def sterm_pretty(sterm: STerm, context: ParenthesisContext = None, depth: int = 0) -> Doc:
    if context is None:
        context = ParenthesisContext(parent_precedence=Precedence.LITERAL, child_side=Side.NONE)

    match sterm:
        case SLiteral(value=value, type=_type):
            if _type == STypeConstructor(Name("String", 0)):
                return text(f'"{value}"')
            return text(str(value))

        case SVar(name=name):
            return text(name.pretty())

        case SHole(name=name):
            return text("?" + name.pretty())

        case SAnnotation(expr=expr, type=_type):
            expr_doc = pretty_sterm_with_parens(expr, ParenthesisContext(Precedence.ANNOTATION, Side.LEFT), depth + 1)
            type_doc = stype_pretty(_type, ParenthesisContext(Precedence.ANNOTATION, Side.RIGHT))
            return group(concat([expr_doc, text(" :"), nest(DEFAULT_TAB_SIZE, concat([line(), type_doc]))]))

        case SIf(cond=cond, then=then, otherwise=otherwise):
            pretty_cond = pretty_sterm_with_parens(cond, ParenthesisContext(Precedence.IF, Side.NONE), depth + 1)
            pretty_then = pretty_sterm_with_parens(then, ParenthesisContext(Precedence.IF, Side.NONE), depth + 1)
            pretty_otherwise = pretty_sterm_with_parens(
                otherwise, ParenthesisContext(Precedence.IF, Side.NONE), depth + 1
            )

            return group(
                concat(
                    [
                        text("if "),
                        pretty_cond,
                        line(),
                        text("then "),
                        nest(DEFAULT_TAB_SIZE, pretty_then),
                        line(),
                        text("else "),
                        nest(DEFAULT_TAB_SIZE, pretty_otherwise),
                    ]
                )
            )

        case SApplication(fun=fun, arg=arg) as term:
            match term:
                case (
                    SApplication(fun=SApplication(fun=SVar(name=op_name), arg=left, loc=_), arg=right, loc=_)
                    | SApplication(
                        fun=SApplication(fun=STypeApplication(body=SVar(name=op_name), type=_), arg=left, loc=_),
                        arg=right,
                        loc=_,
                    )
                ) if op_name.pretty() in AEON_INFIX_OPERATORS:
                    return format_infix_application(left, right, op_name, depth)

            if depth == 0:
                if isinstance(fun, SVar) and fun.name.pretty() == "main":
                    return nil()

            pretty_fun = pretty_sterm_with_parens(fun, ParenthesisContext(Precedence.APPLICATION, Side.LEFT), depth + 1)
            pretty_arg = pretty_sterm_with_parens(
                arg, ParenthesisContext(Precedence.APPLICATION, Side.RIGHT), depth + 1
            )

            return group(concat([pretty_fun, line(), pretty_arg]))

        case SAbstraction(var_name=var_name, body=body):
            pretty_var_name = text(var_name.pretty())
            _left = concat([text("\\"), pretty_var_name, text(" ->")])

            _pretty_body = pretty_sterm_with_parens(body, ParenthesisContext(Precedence.ARROW, Side.RIGHT), depth + 1)

            return group(concat([_left, nest(DEFAULT_TAB_SIZE, concat([line(), _pretty_body]))]))

        case SLet(var_name=var_name, var_value=var_value, body=body):
            pretty_var_name = text(var_name.pretty())
            pretty_var_value = pretty_sterm_with_parens(
                var_value, ParenthesisContext(Precedence.LET, Side.NONE), depth + 1
            )
            pretty_body = pretty_sterm_with_parens(body, ParenthesisContext(Precedence.LET, Side.NONE), depth)

            if depth == 0:
                return group(
                    concat(
                        [
                            text("def "),
                            pretty_var_name,
                            text(" ="),
                            nest(DEFAULT_TAB_SIZE, concat([line(), pretty_var_value])),
                            hard_line(),
                            hard_line(),
                            pretty_body,
                        ]
                    )
                )
            else:
                binding = concat([pretty_var_name, text(" = "), pretty_var_value])
                return group(concat([text("let "), binding, text(" in"), line(), pretty_body]))

        case SRec(var_name=var_name, var_type=var_type, var_value=var_value, body=body):  # refazer rec
            pretty_var_name = text(var_name.pretty())
            pretty_var_type = pretty_stype_with_parens(var_type, ParenthesisContext(Precedence.ANNOTATION, Side.RIGHT))
            pretty_var_value = pretty_sterm_with_parens(
                var_value, ParenthesisContext(Precedence.LET, Side.NONE), depth + 1
            )
            pretty_body = pretty_sterm_with_parens(body, ParenthesisContext(Precedence.LET, Side.NONE), depth)

            if depth != 0:
                pretty_binding = concat([pretty_var_name, text(" : "), pretty_var_type, text(" = "), pretty_var_value])
                return group(concat([text("let "), pretty_binding, text(" in"), line(), pretty_body]))

            match var_type:
                case SAbstractionType() as _type:
                    named_vars, final_type = unwrap_abstraction_types(_type)

                    pretty_func_definition, alignment = pretty_print_function_definition(
                        pretty_var_name, named_vars, final_type
                    )

                    var_value = strip_matching_abstractions(var_value, named_vars)

                    pretty_var_value = pretty_sterm_with_parens(
                        var_value, ParenthesisContext(Precedence.LET, Side.NONE), depth + 1
                    )

                    full_type = group(
                        concat(
                            [
                                pretty_func_definition,
                                text(" {"),
                                nest(DEFAULT_TAB_SIZE, concat([line(), pretty_var_value])),
                                line(),
                                text("}"),
                            ]
                        )
                    )

                case _:
                    def_line = concat([text("def "), pretty_var_name, text(" : ")])
                    full_type = group(
                        concat(
                            [
                                def_line,
                                nest(len("def ") + len(var_name.pretty()) + DEFAULT_TAB_SIZE, pretty_var_type),
                                line(),
                                text("= "),
                                nest(DEFAULT_TAB_SIZE, pretty_var_value),
                            ]
                        )
                    )
            return group(concat([full_type, hard_line(), hard_line(), pretty_body]))

        case STypeAbstraction(name=name, kind=kind, body=body):
            pretty_name = text(name.pretty())
            pretty_kind = text(str(kind))  # should be changed to skind pretty in the future
            pretty_body = pretty_sterm_with_parens(
                body, ParenthesisContext(Precedence.APPLICATION, Side.RIGHT), depth + 1
            )

            pretty_kind_def = concat([pretty_name, text(" : "), pretty_kind])
            pretty_binding = concat([pretty_kind_def, text("."), pretty_body])
            return group(concat([text("ƛ"), pretty_binding]))

        case STypeApplication(body=body, type=_type):
            pretty_body = sterm_pretty(body, ParenthesisContext(Precedence.APPLICATION, Side.LEFT), depth + 1)
            return group(pretty_body)

        case _:
            return text(str(sterm))


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
                simplified_then = normalize_term(then, context, seen)
                return simplified_then
            elif simplified_cond == false:
                simplified_otherwise = normalize_term(otherwise, context, seen)
                return simplified_otherwise
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
            match body:
                case SHole(name=name):
                    return SLet(var_name=name, var_value=normalize_term(var_value, context, seen), body=SVar(name=name))
                case _:
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
            match body:
                case SHole(name=name):
                    return SRec(
                        var_name=name,
                        var_type=var_type,
                        var_value=normalize_term(var_value, context, seen),
                        body=SVar(name=name),
                    )
                case _:
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


def pretty_print_sterm(term: STerm) -> str:
    simplified_term = simplify_sterm(term)
    return str(sterm_pretty(simplified_term))


def simplify_sterm(term: STerm) -> STerm:
    def apply_func(acc: STerm, func: Callable[[STerm], STerm]) -> STerm:
        return func(acc)

    functions: List[Callable[[STerm], STerm]] = [normalize_term, rename_unused_variables]
    return reduce(apply_func, functions, term)


def node_pretty(node: Node) -> Doc:
    match node:
        case ImportAe(path=path, func=func):
            return (
                group(concat([text("import"), line(), text(f'"{path}";')]))
                if not func
                else group(
                    concat([text("import"), line(), text(func), line(), text("from"), line(), text(f'"{path}";')])
                )
            )
        case TypeDecl(name=name):
            return group(concat([text("type"), line(), text(f"{name.pretty()};")]))
        case Decorator(name=name, macro_args=macro_args):
            pretty_macro_args = [sterm_pretty(simplify_sterm(arg)) for arg in macro_args]
            pretty_macro_args_doc = parens(insert_between(concat([text(","), line()]), pretty_macro_args))

            return concat([text("@"), text(name.pretty()), pretty_macro_args_doc])
        case InductiveDecl(name=name, args=args, constructors=constructors, measures=measures):
            pretty_name = concat([text("inductive"), line(), text(name.pretty())])
            pretty_args = group(insert_between(line(), [text(arg.pretty()) for arg in args]))
            pretty_constructors = group(
                insert_between(line(), [concat([text("| "), node_pretty(cons)]) for cons in constructors])
            )
            pretty_measures = group(
                insert_between(line(), [concat([text("+ "), node_pretty(meas)]) for meas in measures])
            )

            return group(insert_between(line(), [pretty_name, pretty_args, pretty_constructors, pretty_measures]))
        case Definition(name=name, foralls=foralls, args=args, type=type_, body=body, decorators=decorators):
            for var_name, _ in reversed(args):
                body = SAbstraction(var_name=var_name, body=body)

            for var_name, var_type in reversed(args):
                type_ = SAbstractionType(var_name=var_name, var_type=var_type, type=type_)

            for type_name, kind in reversed(foralls):
                body = STypeAbstraction(name=type_name, kind=kind, body=body)

            pretty_decorators = insert_between(line(), [node_pretty(decorator) for decorator in decorators])

            match type_:
                case SAbstractionType() as _type:
                    named_vars, final_type = unwrap_abstraction_types(_type)

                    pretty_func_definition, alignment = pretty_print_function_definition(
                        text(name.pretty()), named_vars, final_type
                    )

                    stripped_body = strip_matching_abstractions(body, named_vars)

                    pretty_body = pretty_sterm_with_parens(
                        stripped_body, ParenthesisContext(Precedence.LET, Side.NONE), depth=1
                    )

                    definition_doc = group(
                        concat(
                            [
                                pretty_func_definition,
                                text(" {"),
                                nest(DEFAULT_TAB_SIZE, concat([line(), pretty_body])),
                                line(),
                                text("}"),
                            ]
                        )
                    )

                case _:
                    pretty_var_name = name.pretty()
                    pretty_var_type = stype_pretty(type_)
                    pretty_body = sterm_pretty(body, depth=1)

                    def_line = concat([text("def "), text(pretty_var_name), text(" : ")])

                    definition_doc = group(
                        concat(
                            [
                                def_line,
                                nest(len("def ") + len(pretty_var_name) + DEFAULT_TAB_SIZE, pretty_var_type),
                                line(),
                                text("= "),
                                nest(DEFAULT_TAB_SIZE, pretty_body),
                                text(";"),
                            ]
                        )
                    )

            return group(concat([pretty_decorators, hard_line() if decorators else nil(), definition_doc]))

        case Program(imports=imports, type_decls=type_decls, inductive_decls=inductive_decls, definitions=definitions):
            pretty_blocks = [
                group(insert_between(line(), [node_pretty(_import) for _import in imports])) if imports else nil(),
                group(insert_between(line(), [node_pretty(type_decl) for type_decl in type_decls]))
                if type_decls
                else nil(),
                group(insert_between(line(), [node_pretty(inductive_decl) for inductive_decl in inductive_decls]))
                if inductive_decls
                else nil(),
                group(insert_between(concat([hard_line(), hard_line()]), [node_pretty(defn) for defn in definitions]))
                if definitions
                else nil(),
            ]

            return group(
                insert_between(concat([hard_line(), hard_line()]), [block for block in pretty_blocks if block != nil()])
            )
    return nil()


def pretty_print_node(node: Node) -> str:
    return str(node_pretty(node))
