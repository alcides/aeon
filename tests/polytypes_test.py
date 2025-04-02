from aeon.core.types import TypeConstructor
from aeon.frontend.parser import parse_type

from aeon.sugar.stypes import SBaseType
from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile


def test_polytype():
    t = parse_type("List Int")
    assert isinstance(t, TypeConstructor)


def test_polytypes_e2e():
    source = """
            type List a;
            def a : (List Int) = native "1";
            def b : (l:(List Int)) -> Int = \\x -> 0;
            def c : Int = b a;
        """
    assert check_compile(source, SBaseType("Top"))


def test_polytypes_link():
    source = """
            type List a;
            def k : (List Int) = native "1";
            def k2 : (List Float) = native "1";
            def f : (l:(List a)) -> (List a) = \\x -> x;
            def r : (List Int) = f k;
            def r2 : (List Float) = f k2;
        """
    assert check_compile(source, st_top)

    source = """
            type List a;
            def k : (List Int) = native "1";
            def f : (l:(List a)) -> (List a) = \\x -> x;
            def r : (List Float) = f k;
        """
    assert not check_compile(source, SBaseType("Top"))


def test_polytypes_missing_decl():
    source = """
            def k : (List Int) = native "1";
        """
    assert not check_compile(source, SBaseType("Top"))
