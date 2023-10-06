from __future__ import annotations

from aeon.decorators.decorators_aux import handle_multiple_terms
from aeon.decorators.decorators_aux import handle_term
from aeon.core.terms import Term


def minimize(terms: list[Term]) -> Term:
    """Minimizes a term.

    Args:
        terms (list[Term]): A list containing a single Term to be minimized.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the minimized Term and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not 1.
    """
    assert len(terms) == 1
    return handle_term(terms[0])


def maximize(terms: list[Term]) -> Term:
    """Maximizes a term.

    Args:
        terms (list[Term]): A list containing a single Term to be maximized.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the maximized Term and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not 1.
    """
    assert len(terms) == 1

    return handle_term(terms[0])


def multi_minimize(terms: list[Term]) -> Term:
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

    return handle_term(terms[0])


def multi_maximize(terms: list[Term]) -> Term:
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

    return handle_term(terms[0])


def assert_property(terms: list[Term]) -> Term:
    """Term inside the property decorator is subject of a property-based testing.

    Args:
        terms (list[Term]): A list containing a single Term whose property is to be tested.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the Term to be tested and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not 1.
    """
    assert len(terms) == 1

    return handle_term(terms[0])


def assert_properties(terms: list[Term]) -> Term:
    """Terms inside the properties decorator are subject of property-based testing.

    Args:
        terms (list[Term]): A list containing multiple Terms whose properties are to be tested.

    Returns:
        tuple[Term, list[bool]]: A tuple containing the Terms to be tested and a list of booleans.

    Raises:
        AssertionError: If the length of terms is not greater than 1.
    """
    assert len(terms) > 1

    return handle_multiple_terms(terms)
