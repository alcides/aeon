from typing import Callable, Union

from aeon.core.types import t_int, t_bool
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Let,
    Rec,
    Term,
    Var,
    Literal,
    If,
)


def is_anf(t: Term) -> bool:
    if isinstance(t, Literal):
        return True
    elif isinstance(t, Var):
        return True
    elif isinstance(t, Let):
        return is_anf(t.var_value) and is_anf(t.body)
    elif isinstance(t, Rec):
        return is_anf(t.var_value) and is_anf(t.body)
    elif isinstance(t, Application):
        return is_anf(t.fun) and (isinstance(t.arg, Var) or isinstance(t.arg, Literal))
    elif isinstance(t, If):
        return (
            (isinstance(t.cond, Var) or isinstance(t.cond, Literal))
            and is_anf(t.then)
            and is_anf(t.otherwise)
        )
    elif isinstance(t, Annotation):
        return is_anf(t.expr)
    elif isinstance(t, Abstraction):
        return is_anf(t.body)
    else:
        assert False


def ensure_anf_app(fresh: Callable[[], str], t: Application) -> Term:
    if isinstance(t.fun, Let):
        return Let(
            t.fun.var_name,
            t.fun.var_value,
            ensure_anf_app(fresh, Application(t.fun.body, t.arg)),
        )
    if isinstance(t.arg, Var) or isinstance(t.arg, Literal):
        return t
    else:
        v = fresh()
        return ensure_anf_let(Let(v, t.arg, Application(t.fun, Var(v))))


def ensure_anf_if(fresh: Callable[[], str], t: If) -> Term:
    if isinstance(t.cond, Var) or isinstance(t.cond, Literal):
        return t
    else:
        v = fresh()
        return ensure_anf_let(Let(v, t.cond, If(Var(v), t.then, t.otherwise)))


def mk_binop(fresh: Callable[[], str], op: str, a1: Term, a2: Term) -> Term:
    return ensure_anf_app(
        fresh, Application(ensure_anf_app(fresh, Application(Var(op), a1)), a2)
    )


"""
    let x = (let y = 1 in y) in x

    let y = 1 in (let x = y in x)
"""


def ensure_anf_let(t: Let) -> Term:
    if isinstance(t.var_value, Let):
        inner = t.var_value
        assert inner.var_name != t.var_name

        b = inner.var_value
        if isinstance(b, Let):
            b = ensure_anf_let(inner.var_value)
        if isinstance(b, Rec):
            b = ensure_anf_rec(inner.var_value)

        return Let(
            inner.var_name,
            b,
            ensure_anf_let(Let(t.var_name, inner.body, t.body)),
        )
    elif isinstance(t.var_value, Rec):
        inner = t.var_value
        assert inner.var_name != t.var_name

        b = inner.var_value
        if isinstance(b, Let):
            b = ensure_anf_let(inner.var_value)
        if isinstance(b, Rec):
            b = ensure_anf_rec(inner.var_value)

        return Rec(
            inner.var_name,
            inner.var_type,
            b,
            ensure_anf_let(Let(t.var_name, inner.body, t.body)),
        )
    else:
        return t


def ensure_anf_rec(t: Rec) -> Term:
    if isinstance(t.var_value, Let):
        inner = t.var_value
        assert inner.var_name != t.var_name

        b = inner.var_value
        if isinstance(b, Let):
            b = ensure_anf_let(inner.var_value)
        if isinstance(b, Rec):
            b = ensure_anf_rec(inner.var_value)

        return Let(
            inner.var_name,
            b,
            ensure_anf_rec(Rec(t.var_name, t.var_type, inner.body, t.body)),
        )
    elif isinstance(t.var_value, Rec):
        inner = t.var_value
        assert inner.var_name != t.var_name

        b = inner.var_value
        if isinstance(b, Let):
            b = ensure_anf_let(inner.var_value)
        if isinstance(b, Rec):
            b = ensure_anf_rec(inner.var_value)

        return Rec(
            inner.var_name,
            inner.var_type,
            b,
            ensure_anf_rec(Rec(t.var_name, t.var_type, inner.body, t.body)),
        )
    else:
        return t


true = Literal(True, t_bool)
false = Literal(False, t_bool)

i0 = Literal(0, t_int)
i1 = Literal(1, t_int)
i2 = Literal(2, t_int)
