from __future__ import annotations

from aeon.core.terms import Let
from aeon.core.terms import Term
from aeon.core.terms import Var


def handle_term(term: Term, minimize_flag: bool) -> tuple[Term, bool | list[bool]]:
    if isinstance(term, Let):
        return term, minimize_flag
    elif isinstance(term, Var):
        # TODO: handle Var type here
        pass
    raise Exception(f"Term not handled by annotation: {type(term)}")
