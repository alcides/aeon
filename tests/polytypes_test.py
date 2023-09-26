from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import TypeConstructor
from aeon.frontend.parser import parse_type
from aeon.verification.sub import sub
from aeon.verification.vcs import LiquidConstraint


def test_polytype():
    t = parse_type("List Int")
    assert isinstance(t, TypeConstructor)

    t2 = parse_type("List Int")
    assert sub(t, t2)

    t3 = parse_type("List Float")
    assert sub(t, t3) == LiquidConstraint(LiquidLiteralBool(False))
