from __future__ import annotations

from typing import Callable

from aeon.core.terms import Application
from aeon.core.terms import Literal
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.utils.name import Name


def mk_binop(fresh: Callable[[], str], op: str, a1: Term, a2: Term) -> Term:
    return Application(Application(Var(Name(op, 0)), a1), a2)


true = Literal(True, t_bool)
false = Literal(False, t_bool)

i0 = Literal(0, t_int)
i1 = Literal(1, t_int)
i2 = Literal(2, t_int)
