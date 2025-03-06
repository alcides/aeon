from aeon.core.types import TypeConstructor
from aeon.frontend.parser import parse_type

from aeon.sugar.stypes import SBaseType
from tests.driver import check_compile


def test_polytype():
    t = parse_type("List Int")
    assert isinstance(t, TypeConstructor)


def test_polytypes_e2e():
    source = """
            def a : (List Int) = native "1";
            def b : (l:(List Int)) -> Int = \\x -> 0;
            def c : Int = b a;
        """
    assert check_compile(source, SBaseType("Top"))
