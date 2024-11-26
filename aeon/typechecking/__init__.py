from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.elaboration import UnificationException, elaborate
from aeon.typechecking.entailment import entailment
from aeon.typechecking.typeinfer import (
    CouldNotGenerateConstraintException,
    FailedConstraintException,
    check,
    check_type,
)


def elaborate_and_check(ctx: TypingContext, term: Term,
                        expected_type: Type) -> bool:
    try:
        p = elaborate(ctx, term, expected_type)
    except UnificationException:
        return False
    return check_type(ctx, p, expected_type)


def elaborate_and_check_type_errors(
    ctx: TypingContext,
    term: Term,
    expected_type: Type,
) -> list[Exception | str]:
    """Checks whether t as type ty in ctx, but returns a list of errors."""
    try:
        p = elaborate(ctx, term, expected_type)
    except UnificationException as e:
        return [e]

    try:
        constraint = check(ctx, p, expected_type)
        r = entailment(ctx, constraint)
        if r:
            return []
        else:
            return [
                "Could not prove typing relation.",
                f"Context: {ctx}",
                f"Term: {term}",
                f"Type: {expected_type}",
            ]
    except CouldNotGenerateConstraintException as e:
        return [e]
    except FailedConstraintException as e:
        return [e]
