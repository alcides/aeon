from __future__ import annotations

from aeon.core.terms import Application
from aeon.core.terms import Let
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.utils.ast_helpers import ensure_anf_app


def minimize(term: Term) -> Term:
    if isinstance(term, Var):
        # TODO: Calculate the difference bewtween the minimum value and the variable
        #  then return that binary expression in the anf format
        raise Exception("Term not handled by @minimize annotation")

    elif isinstance(term, (Application, Let)):

        return term

    raise Exception("Term not handled by @minimize annotation " + str(type(term)))


def maximize(term: Term) -> Term:
    if isinstance(term, Var):
        # TODO: Calculate the difference bewtween the maximumvalue and the variable
        #  then return that binary expression in the anf format
        raise Exception("Term not handled by @maximize annotation")

    elif isinstance(term, (Application, Let)):
        return term

    raise Exception("Term not handled by @maximize annotation " + str(type(term)))


def multi_minimize(term: Term) -> Term:
    return term


def multi_maximize(term: Term) -> Term:
    return term
