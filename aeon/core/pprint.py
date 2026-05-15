from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import AbstractionType
from aeon.core.types import TypeConstructor
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import TypeVar
from aeon.core.types import type_free_term_vars

aeon_prelude_ops_to_text = {
    "%": "mod",
    "/": "div",
    "*": "mul",
    "-": "sub",
    "+": "add",
    "%.": "modf",
    "/.": "divf",
    "*.": "mulf",
    "-.": "subf",
    "+.": "addf",
    ">=": "gte",
    ">": "gt",
    "<=": "lte",
    "<": "lt",
    "!=": "ne",
    "==": "eq",
    "&&": "and",
    "||": "or",
    "!": "not",
}


def pretty_print(t: Type) -> str:
    if isinstance(t, TypeConstructor):
        return str(t)
    elif isinstance(t, TypeVar):
        return str(t)
    elif isinstance(t, AbstractionType):
        at = pretty_print(t.var_type)
        rt = pretty_print(t.type)
        if t.var_name in type_free_term_vars(t.var_type):
            return f"""(
                {t.var_name}:{at}) -> {rt}"""
        else:
            return f"""{at} -> {rt}"""
    elif isinstance(t, RefinedType):
        it = pretty_print(t.type)
        if t.refinement == LiquidLiteralBool(True):
            return it
        else:
            return f"{{{t.name}:{it} | {t.refinement}}}"
    raise ValueError(f"Unknown type {t}")


def pretty_print_term(term: Term):
    term_str: str = custom_preludes_ops_representation(term)[0]
    print(term_str)


def operator_name(term: Term) -> str | None:
    """The prelude operator name if `term` is a (possibly type-applied) operator variable."""
    inner: Term = term
    while isinstance(inner, TypeApplication):
        inner = inner.body
    if isinstance(inner, Var) and inner.name.name in aeon_prelude_ops_to_text:
        return inner.name.name
    return None


def custom_preludes_ops_representation(term: Term, counter: int = 0) -> tuple[str, int]:
    match term:
        # Fully applied binary operator: ((op left) right) -> (left op right)
        case Application(fun=Application(fun=opfun, arg=left), arg=right) if (
            op := operator_name(opfun)
        ) is not None and op != "!":
            left_str, counter = custom_preludes_ops_representation(left, counter)
            right_str, counter = custom_preludes_ops_representation(right, counter)
            return f"({left_str} {op} {right_str})", counter

        # Fully applied unary operator: (! arg)
        case Application(fun=opfun, arg=arg) if operator_name(opfun) == "!":
            arg_str, counter = custom_preludes_ops_representation(arg, counter)
            return f"(!{arg_str})", counter

        # Partially applied binary operator: (op left) -> (\v -> left op v)
        case Application(fun=opfun, arg=left) if (op := operator_name(opfun)) is not None and op != "!":
            left_str, counter = custom_preludes_ops_representation(left, counter)
            counter += 1
            assert op is not None
            new_var_name = f"__{aeon_prelude_ops_to_text[op]}_{counter}__"
            return f"(\\{new_var_name} -> {left_str} {op} {new_var_name})", counter

        case Application(fun=fun, arg=arg):
            fun_str, counter = custom_preludes_ops_representation(fun, counter)
            arg_str, counter = custom_preludes_ops_representation(arg, counter)
            return f"({fun_str} {arg_str})", counter

        case Annotation(expr=expr, type=type):
            expr_str, counter = custom_preludes_ops_representation(expr, counter)
            return f"""({expr_str} : {type})""", counter

        case Abstraction(var_name=var_name, body=body):
            body_str, counter = custom_preludes_ops_representation(body, counter)
            return f"""(\\{var_name} -> {body_str})""", counter

        case Let(var_name=var_name, var_value=var_value, body=body):
            var_value_str, counter = custom_preludes_ops_representation(var_value, counter)
            body_str, counter = custom_preludes_ops_representation(body, counter)
            return f"""(let {var_name} = {var_value_str} in\n {body_str})""", counter

        case Rec(var_name=var_name, var_type=var_type, var_value=var_value, body=body, decreasing_by=_):
            var_value_str, counter = custom_preludes_ops_representation(var_value, counter)
            body_str, counter = custom_preludes_ops_representation(body, counter)
            return f"""(let {var_name} : {var_type} = {var_value_str} in\n {body_str})""", counter

        case If(cond=cond, then=then, otherwise=otherwise):
            cond_str, counter = custom_preludes_ops_representation(cond, counter)
            then_str, counter = custom_preludes_ops_representation(then, counter)
            otherwise_str, counter = custom_preludes_ops_representation(otherwise, counter)
            return f"""(if {cond_str} then {then_str} else {otherwise_str})""", counter

        case TypeAbstraction(name=name, kind=kind, body=body):
            body_str, counter = custom_preludes_ops_representation(body, counter)
            return f"""ƛ{name}:{kind}.({body_str})""", counter

        case RefinementAbstraction(name=name, sort=sort, body=body):
            body_str, counter = custom_preludes_ops_representation(body, counter)
            return f"""Λρ{name}:({sort}).({body_str})""", counter

        case TypeApplication(body=body, type=type):
            body_str, counter = custom_preludes_ops_representation(body, counter)
            return f"""({body_str})[{type}]""", counter

        case RefinementApplication(body=body, refinement=refinement):
            body_str, counter = custom_preludes_ops_representation(body, counter)
            ref_str, counter = custom_preludes_ops_representation(refinement, counter)
            return f"""({body_str})[{{{ref_str}}}]""", counter

        case Literal(_, _) | Var(_) | Hole(_):
            return str(term), counter

    return str(term), counter
