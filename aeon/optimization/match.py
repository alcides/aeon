from __future__ import annotations

import ast

from aeon.core.terms import Abstraction, Application, Term, TypeApplication, Var
from aeon.core.types import Type
from aeon.optimization.native import literal_from_python, native_code, native_term
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


def handler_arity(handler: Term) -> int:
    n = 0
    cur = handler
    while isinstance(cur, Abstraction):
        n += 1
        cur = cur.body
    return n


def scrutinee_fields(scrutinee: Term, arity: int) -> list[Term] | None:
    """Field projections for a scrutinee, when its constructor shape is known or a bare variable."""
    if (shape := recognize_constructor(scrutinee)) is not None:
        _, _, args = shape
        if len(args) == arity:
            return args
        return None
    head = strip_type_wrappers(scrutinee)
    if isinstance(head, Var):
        name = head.name.name
        return [native_term(f"{name}[{i + 1}]") for i in range(arity)]
    return None


def is_uni_constructor(type_name: str) -> bool:
    order = get_constructor_order(type_name)
    return order is not None and len(order) == 1


def optimize_destructor_let(type_name: str, scrutinee: Term, handler: Term) -> Term | None:
    """Optimize ``let (C x …) := scrut in body`` for single-constructor types.

    When the scrutinee is a known constructor application (or native tuple),
    apply the handler to its fields. When the scrutinee is still a variable,
    project fields via native tuple indexing — every value of a
    uni-constructor type carries the same runtime representation.
    """
    order = get_constructor_order(type_name)
    if order is None or len(order) != 1:
        return None
    arity = handler_arity(handler)
    fields = scrutinee_fields(scrutinee, arity)
    if fields is None:
        return None
    if (shape := recognize_constructor(scrutinee)) is not None:
        scr_type, _, _ = shape
        if scr_type != type_name:
            return None
        key = _constructor_key(scr_type, shape[1])
        if key != order[0]:
            return None
    return apply_handler(handler, fields)


def optimize_eliminator(t: Term) -> Term | None:
    """Select a ``match`` branch when the scrutinee constructor is known."""
    parsed = parse_recursor_app(t)
    if parsed is None:
        return None
    type_name, _, value_args = parsed
    scrutinee, *handlers = value_args
    order = get_constructor_order(type_name)
    if order is None:
        return None

    if len(order) == 1 and len(handlers) == 1:
        if (reduced := optimize_destructor_let(type_name, scrutinee, handlers[0])) is not None:
            return reduced

    shape = recognize_constructor(scrutinee)
    if shape is None:
        return None
    scr_type, constructor_name, ctor_args = shape
    if scr_type != type_name:
        return None
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
