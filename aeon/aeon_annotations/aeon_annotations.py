from __future__ import annotations

from aeon.aeon_annotations.annotations_aux import handle_mutiple_terms
from aeon.aeon_annotations.annotations_aux import handle_term
from aeon.core.terms import Literal
from aeon.core.terms import Term
from aeon.core.types import BaseType


def minimize(terms: list[Term]) -> tuple[Term, list[bool]]:
    assert len(terms) == 1
    return handle_term(terms[0], [True])


def maximize(terms: list[Term]) -> tuple[Term, list[bool]]:
    assert len(terms) == 1
    return handle_term(terms[0], [False])


def multi_minimize(terms: list[Term]) -> tuple[Term, list[bool]]:
    assert len(terms) == 2
    assert isinstance(terms[1], Literal) and terms[1].type == BaseType("Int")
    assert terms[1].value > 0  # type: ignore[operator]

    return handle_term(terms[0], [True] * terms[1].value)  # type: ignore[operator]


def multi_maximize(terms: list[Term]) -> tuple[Term, list[bool]]:
    assert len(terms) == 2
    assert isinstance(terms[1], Literal) and terms[1].type == BaseType("Int")
    assert terms[1].value > 0  # type: ignore[operator]

    return handle_term(terms[0], [False] * terms[1].value)  # type: ignore[operator]


def property(terms: list[Term]) -> tuple[Term, list[bool]]:
    assert len(terms) == 1

    return handle_term(terms[0], [False])


def properties(terms: list[Term]) -> tuple[Term, list[bool]]:
    assert len(terms) > 1

    return handle_mutiple_terms(terms, [False] * len(terms))
