from __future__ import annotations

import ast

from aeon.core.terms import Abstraction, Application, Literal, Term, TypeApplication, Var
from aeon.core.types import Type
from aeon.optimization.native import literal_from_python, native_code
from aeon.optimization.whnf import strip_type_wrappers
from aeon.utils.name import Name
from aeon.verification.constructor_registry import get_constructor_order


def unfold_application_spine(t: Term) -> tuple[Term, list[Term]]:
    args: list[Term] = []
    cur = t
    while isinstance(cur, Application):
        args.append(cur.arg)
        cur = cur.fun
    args.reverse()
    return strip_type_wrappers(cur), args


def _constructor_key(type_name: str, constructor_name: str) -> str:
    return f"{type_name}_{constructor_name}"


def _split_constructor_name(name: str) -> tuple[str, str] | None:
    if "_" not in name:
        return None
    type_name, constructor_name = name.split("_", 1)
    return type_name, constructor_name


def _known_constructor_key(key: str) -> bool:
    if "_" not in key:
        return False
    type_name, _ = key.split("_", 1)
    order = get_constructor_order(type_name)
    return order is not None and key in order


def _recognize_native_tuple(t: Term) -> tuple[str, str, list[Term]] | None:
    code = native_code(t)
    if code is None:
        return None
    try:
        expr = ast.parse(code, mode="eval").body
    except SyntaxError:
        return None
    if not isinstance(expr, ast.Tuple) or not expr.elts:
        return None
    tag = expr.elts[0]
    if not isinstance(tag, ast.Constant) or not isinstance(tag.value, str):
        return None
    key = tag.value
    if not _known_constructor_key(key):
        return None
    type_name, constructor_name = key.split("_", 1)
    args: list[Term] = []
    for elt in expr.elts[1:]:
        match elt:
            case ast.Constant(value=value):
                args.append(literal_from_python(value))
            case ast.Name(id=name):
                args.append(Var(Name(name)))
            case _:
                return None
    return type_name, constructor_name, args


def recognize_constructor(t: Term) -> tuple[str, str, list[Term]] | None:
    """When ``t`` has a known inductive constructor shape, return its parts."""
    if (native_shape := _recognize_native_tuple(strip_type_wrappers(t))) is not None:
        return native_shape

    head, args = unfold_application_spine(t)
    if not isinstance(head, Var):
        return None
    split = _split_constructor_name(head.name.name)
    if split is None:
        return None
    type_name, constructor_name = split
    key = _constructor_key(type_name, constructor_name)
    if not _known_constructor_key(key):
        return None
    return type_name, constructor_name, args


def parse_recursor_app(t: Term) -> tuple[str, list[Type], list[Term]] | None:
    """Parse a fully-applied ``T_rec`` eliminator application."""
    value_args: list[Term] = []
    cur = strip_type_wrappers(t)
    while isinstance(cur, Application):
        value_args.append(cur.arg)
        cur = cur.fun
    value_args.reverse()
    if len(value_args) < 2:
        return None

    type_args: list[Type] = []
    head = cur
    while isinstance(head, TypeApplication):
        type_args.append(head.type)
        head = head.body
    head = strip_type_wrappers(head)
    if not isinstance(head, Var) or not head.name.name.endswith("_rec"):
        return None

    type_name = head.name.name[: -len("_rec")]
    order = get_constructor_order(type_name)
    if order is None:
        return None
    handlers = value_args[1:]
    if len(handlers) != len(order):
        return None
    return type_name, type_args, value_args


def apply_handler(handler: Term, args: list[Term]) -> Term:
    result = handler
    for arg in args:
        result = Application(result, arg)
    return result


def optimize_eliminator(t: Term) -> Term | None:
    """Select a ``match`` branch when the scrutinee constructor is known."""
    parsed = parse_recursor_app(t)
    if parsed is None:
        return None
    type_name, _, value_args = parsed
    scrutinee, *handlers = value_args
    shape = recognize_constructor(scrutinee)
    if shape is None:
        return None
    scr_type, constructor_name, ctor_args = shape
    if scr_type != type_name:
        return None
    order = get_constructor_order(type_name)
    assert order is not None
    key = _constructor_key(type_name, constructor_name)
    try:
        handler_index = order.index(key)
    except ValueError:
        return None
    return apply_handler(handlers[handler_index], ctor_args)


def optimize_eliminator_abstraction(t: Term) -> Term | None:
    """Peel a leading ``fun ret =>`` wrapper around a fully-applied eliminator."""
    if not isinstance(t, Abstraction):
        return None
    body = t.body
    while isinstance(body, Abstraction):
        body = body.body
    if (reduced := optimize_eliminator(body)) is None:
        return None
    return reduced
