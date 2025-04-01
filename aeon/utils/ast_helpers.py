from __future__ import annotations

from typing import Callable

from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.utils.name import Name


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
            (
                isinstance(t.cond, Var)
                or isinstance(
                    t.cond,
                    Literal,
                )
            )
            and is_anf(t.then)
            and is_anf(t.otherwise)
        )
    elif isinstance(t, Annotation):
        return is_anf(t.expr)
    elif isinstance(t, Abstraction):
        return is_anf(t.body)
    else:
        assert False


def mk_binop(fresh: Callable[[], str], op: str, a1: Term, a2: Term) -> Term:
    return Application(Application(Var(Name(op)), a1), a2)


true = Literal(True, t_bool)
false = Literal(False, t_bool)

i0 = Literal(0, t_int)
i1 = Literal(1, t_int)
i2 = Literal(2, t_int)
