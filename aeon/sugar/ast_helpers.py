from typing import Callable

from aeon.sugar.program import SApplication, SLiteral, STerm, SVar
from aeon.sugar.stypes import STypeConstructor
from aeon.utils.name import Name


def mk_binop(fresh: Callable[[], str], op: Name, a1: STerm, a2: STerm) -> STerm:
    return SApplication(SApplication(SVar(op), a1), a2)


st_top = STypeConstructor(Name("Top", 0))
st_unit = STypeConstructor(Name("Unit", 0))
st_bool = STypeConstructor(Name("Bool", 0))
st_int = STypeConstructor(Name("Int", 0))
st_float = STypeConstructor(Name("Float", 0))
st_string = STypeConstructor(Name("String", 0))

true = SLiteral(True, st_bool)
false = SLiteral(False, st_bool)

i0 = SLiteral(0, st_int)
i1 = SLiteral(1, st_int)
i2 = SLiteral(2, st_int)
