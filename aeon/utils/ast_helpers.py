from typing import Callable

from aeon.core.types import t_int, t_bool
from aeon.core.terms import Abstraction, Application, Let, Rec, Term, Var, Literal, If


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
    elif isinstance(t, Abstraction):
        return is_anf(t.body)
    else:
        assert False


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


def mk_binop(fresh: Callable[[], str], op: str, a1: Term, a2: Term) -> Application:
    return ensure_anf_app(
        fresh, Application(ensure_anf_app(fresh, Application(Var(op), a1)), a2)
    )


true = Literal(True, t_bool)
false = Literal(False, t_bool)

i0 = Literal(0, t_int)
i1 = Literal(1, t_int)
i2 = Literal(2, t_int)
