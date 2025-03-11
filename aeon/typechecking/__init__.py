from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.typechecking.typeinfer import (
    CouldNotGenerateConstraintException,
    FailedConstraintException,
    check,
)


def check_type_errors(
    ctx: TypingContext,
    term: Term,
    expected_type: Type,
) -> list[Exception | str]:
    try:
        constraint = check(ctx, term, expected_type)
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
