from aeon.core.types import TypeConstructor
from aeon.frontend.parser import parse_type
from aeon.verification.sub import sub


def test_polytype():
    t = parse_type("List Int")
    assert isinstance(t, TypeConstructor)

    t2 = parse_type("List Int")

    assert sub(t, t2)
