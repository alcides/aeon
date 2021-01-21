from aeon.core.types import t_int, t_bool
from aeon.core.terms import Application, Term, Var, Literal


def mk_binop(op: str, a1: Term, a2: Term) -> Application:
    return Application(Application(Var(op), a1), a2)


true = Literal(True, t_bool)
false = Literal(False, t_bool)

i0 = Literal(0, t_int)
i1 = Literal(1, t_int)
i2 = Literal(2, t_int)
