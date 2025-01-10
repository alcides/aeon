from typing import Callable

from aeon.sugar.program import SApplication, SLiteral, STerm, SVar
from aeon.sugar.stypes import SBaseType


def mk_binop(fresh: Callable[[], str], op: str, a1: STerm, a2: STerm) -> STerm:
    return SApplication(SApplication(SVar(op), a1), a2)


t_bool = SBaseType("Bool")
t_int = SBaseType("Int")
true = SLiteral(True, t_bool)
false = SLiteral(False, t_bool)

i0 = SLiteral(0, t_int)
i1 = SLiteral(1, t_int)
i2 = SLiteral(2, t_int)
