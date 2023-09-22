from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.elaboration import UnificationException, elaborate
from aeon.typechecking.typeinfer import check_type


def elaborate_and_check(ctx: TypingContext, term: Term,
                        expected_type: Type) -> bool:
    try:
        p = elaborate(ctx, term, expected_type)
    except UnificationException:
        return False
    return check_type(ctx, p, expected_type)
