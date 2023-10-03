from __future__ import annotations

from aeon.decorators.decorators_aux import handle_multiple_terms
from aeon.decorators.decorators_aux import handle_term
from aeon.core.terms import Literal
from aeon.core.terms import Term
from aeon.core.types import BaseType


def minimize(terms: list[Term]) -> tuple[Term, bool]:
    """Minimizes a term.

    Args:
        terms (list[Term]): A list containing a single Term to be minimized.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the minimized Term and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not 1.
    """
    assert len(terms) == 1
    return handle_term(terms[0]), True


def maximize(terms: list[Term]) -> tuple[Term, bool]:
    """Maximizes a term.

    Args:
        terms (list[Term]): A list containing a single Term to be maximized.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the maximized Term and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not 1.
    """
    assert len(terms) == 1
    return handle_term(terms[0]), False


def multi_minimize(terms: list[Term]) -> tuple[Term, list[bool]]:
    """Minimizes a term multiple times based on the value of the second term.

    Args:
        terms (list[Term]): A list containing two Terms, the term to be minimized, and a Literal indicating the
        number of times to minimize.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the minimized Term and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not 2 or the second term is not a positive integer Literal.
    """
    assert len(terms) == 2
    term_literal = terms[1]
    assert isinstance(term_literal, Literal) and term_literal.type == BaseType("Int")
    assert term_literal.value > 0  # type: ignore[operator]

    return handle_term(terms[0]), [True] * term_literal.value  # type: ignore[operator]


def multi_maximize(terms: list[Term]) -> tuple[Term, list[bool]]:
    """Maximizes a term multiple times based on the value of the second term.

    Args:
        terms (list[Term]): A list containing two Terms, the term to be maximized, and a Literal indicating the
        number of times to maximize.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the maximized Term and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not 2 or the second term is not a positive integer Literal.
    """
    assert len(terms) == 2
    term_literal = terms[1]
    assert isinstance(term_literal, Literal) and term_literal.type == BaseType("Int")
    assert term_literal.value > 0  # type: ignore[operator]

    return handle_term(terms[0]), [False] * term_literal.value  # type: ignore[operator]


def assert_property(terms: list[Term]) -> tuple[Term, bool]:
    """Term inside the property decorator is subject of a property-based testing.

    Args:
        terms (list[Term]): A list containing a single Term whose property is to be tested.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the Term to be tested and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not 1.
    """
    assert len(terms) == 1

    return handle_term(terms[0]), False


def assert_properties(terms: list[Term]) -> tuple[Term, list[bool]]:
    """Terms inside the properties decorator are subject of property-based testing.

    Args:
        terms (list[Term]): A list containing multiple Terms whose properties are to be tested.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the Terms to be tested and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not greater than 1.
    """
    assert len(terms) > 1

    return handle_multiple_terms(terms), [False] * len(terms)
