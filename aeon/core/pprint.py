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
from aeon.utils.name import Name

ops_to_abstraction: dict[str, str] = {
    "%": "Int) -> Int",
    "/": "Int) -> Int",
    "*": "Int) -> Int",
    "-": "Int) -> Int",
    "+": "Int) -> Int",
    ">=": "Int) -> Bool",
    ">": "Int) -> Bool",
    "<=": "Int) -> Bool",
    "<": "Int) -> Bool",
    "!=": "Int) -> Bool",
    "==": "Int) -> Bool",
}

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
    match t:
        case TypeConstructor() | TypeVar():
            return str(t)
        case AbstractionType(var_name=vn, var_type=vt, type=rt):
            at = pretty_print(vt)
            rts = pretty_print(rt)
            if vn in type_free_term_vars(vt):
                return f"""(
                {vn}:{at}) -> {rts}"""
            return f"""{at} -> {rts}"""
        case RefinedType(name=n, type=ity, refinement=ref):
            it = pretty_print(ity)
            if ref == LiquidLiteralBool(True):
                return it
            return f"{{{n}:{it} | {ref}}}"
        case _:
            raise ValueError(f"Unknown type {t}")


def pretty_print_term(term: Term):
    term_str: str = custom_preludes_ops_representation(term)[0]
    print(term_str)


def custom_preludes_ops_representation(term: Term, counter: int = 0) -> tuple[str, int]:
    prelude_operations: dict[str, str] = aeon_prelude_ops_to_text
    match term:
        case Application(fun=Var(name=Name(var_name, _)), arg=arg) if var_name in prelude_operations.keys():
            op = var_name
            arg_str, counter = custom_preludes_ops_representation(arg, counter)
            counter += 1
            new_var_name = f"__{prelude_operations[op]}_{counter}__"
            abstraction_type_str = f"({new_var_name}:{ops_to_abstraction[op]}"
            personalized_op = f": {abstraction_type_str} = (\\{new_var_name} -> {arg_str} {op} {new_var_name})"
            return personalized_op, counter

        case Application(fun=fun, arg=arg):
            fun_str, counter = custom_preludes_ops_representation(fun, counter)
            arg_str, counter = custom_preludes_ops_representation(arg, counter)
            return (
                f"""= ({fun_str} {arg_str}
            )""",
                counter,
            )

        case Annotation(expr=expr, type=type):
            expr_str, counter = custom_preludes_ops_representation(expr, counter)
            return f"""({expr_str} : {type})""", counter

        case Abstraction(var_name=var_name, body=body):
            body_str, counter = custom_preludes_ops_representation(body, counter)
            return f"""(\\{var_name} -> {body_str})""", counter

        case Let(var_name=var_name, var_value=var_value, body=body):
            var_value_prefix = "= " if not isinstance(var_value, Application) else ""
            var_value_str, counter = custom_preludes_ops_representation(var_value, counter)
            body_str, counter = custom_preludes_ops_representation(body, counter)
            return f"""(let {var_name} {var_value_prefix}{var_value_str} in\n {body_str})""", counter

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
