from __future__ import annotations

from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import TypeAbstraction
from aeon.core.terms import TypeApplication
from aeon.core.terms import Var
from aeon.core.types import BaseKind
from aeon.core.types import get_type_vars
from aeon.core.types import TypePolymorphism


def elaboration(e: Term) -> Term:
    if isinstance(e, Literal):
        return e
    elif isinstance(e, Hole):
        return e
    elif isinstance(e, Var):
        return e
    elif isinstance(e, Annotation):
        return e
    elif isinstance(e, Application):
        return e
    elif isinstance(e, Abstraction):
        return e
    elif isinstance(e, Let):
        return e
    elif isinstance(e, Rec):
        e1: Rec = e
        if len(get_type_vars(e.var_type)) > 0:
            nt = e.var_type
            nv = e.var_value
            for typevar in get_type_vars(e.var_type):
                nt = TypePolymorphism(name=typevar.name, kind=BaseKind(), body=nt)
                nv = TypeAbstraction(name=typevar.name, kind=BaseKind(), body=nv)

            e1 = Rec(e.var_name, nt, nv, e.body)

        return e1
    elif isinstance(e, If):
        return e
    elif isinstance(e, TypeApplication):
        return e
    elif isinstance(e, TypeAbstraction):
        return e
    else:
        raise NotImplementedError()
