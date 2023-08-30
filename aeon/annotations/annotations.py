from __future__ import annotations

from aeon.core.terms import Application
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import BaseType


def minimize(terms: list[Term]) -> tuple[Term, bool]:
    assert len(terms) == 1
    minimize_term = terms[0]

    if isinstance(minimize_term, Let):
        return minimize_term, True
    elif isinstance(minimize_term, Var):
        # TODO: Calculate the difference bewtween the minimum value and the variable
        #  then return that binary expression in the anf format
        pass

    raise Exception("Term not handled by @minimize annotation " + str(type(minimize_term)))


def maximize(terms: list[Term]) -> tuple[Term, bool]:
    assert len(terms) == 1
    maximize_term = terms[0]
    if isinstance(maximize_term, (Application, Let)):

        return maximize_term, False
    elif isinstance(maximize_term, Var):
        # TODO: Calculate the difference bewtween the minimum value and the variable
        #  then return that binary expression in the anf format
        pass

    raise Exception("Term not handled by @minimize annotation " + str(type(maximize_term)))


def multi_minimize(terms: list[Term]) -> tuple[Term, list[bool]]:
    assert len(terms) == 2
    multi_minimize_term = terms[0]
    assert isinstance(terms[1], Literal) and terms[1].type == BaseType("Int")

    minimize_list_length = terms[1].value
    minimize_list = [True for _ in range(minimize_list_length)]
    assert len(minimize_list) > 0

    return multi_minimize_term, minimize_list


def multi_maximize(terms: list[Term]) -> tuple[Term, list[bool]]:
    assert len(terms) == 2
    multi_maximize_term = terms[0]
    assert isinstance(terms[1], Literal) and terms[1].type == BaseType("Int")

    minimize_list_length = terms[1].value
    minimize_list = [False for _ in range(minimize_list_length)]
    assert len(minimize_list) > 0

    return multi_maximize_term, minimize_list
