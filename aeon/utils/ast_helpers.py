from typing import Callable

from aeon.core.types import t_int, t_bool
from aeon.core.terms import Application, Let, Term, Var, Literal, If


def ensure_anf_app(fresh: Callable[[], str], t: Application) -> Term:
    if isinstance(t.arg, Var) or isinstance(t.arg, Literal):
        return t
    else:
        v = fresh()
        return Let(v, t.arg, Application(t.fun, Var(v)))


def ensure_anf_if(fresh: Callable[[], str], t: If) -> Term:
    if isinstance(t.cond, Var) or isinstance(t.cond, Literal):
        return t
    else:
        v = fresh()
        return Let(v, t.cond, If(Var(v), t.then, t.otherwise))


def mk_binop(fresh: Callable[[], str], op: str, a1: Term,
             a2: Term) -> Application:
    return ensure_anf_app(
        fresh, Application(ensure_anf_app(fresh, Application(Var(op), a1)),
                           a2))


true = Literal(True, t_bool)
false = Literal(False, t_bool)

i0 = Literal(0, t_int)
i1 = Literal(1, t_int)
i2 = Literal(2, t_int)
