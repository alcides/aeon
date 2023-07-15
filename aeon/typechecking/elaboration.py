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
        if contains_type_var(e.var_type):
            print("Should introduce forall!")
        return e
    elif isinstance(e, If):
        return e
    elif isinstance(e, TypeApplication):
        return e
    elif isinstance(e, TypeAbstraction):
        return e
    else:
        raise NotImplementedError()
