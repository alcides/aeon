from __future__ import annotations

from aeon.core.terms import Rec
from aeon.core.types import BaseKind
from aeon.core.types import get_type_vars
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.elaboration import elaborate_check
from aeon.typechecking.elaboration import elaborate_foralls
from aeon.typechecking.elaboration import elaborate_remove_unification


def help_type_vars(t: str) -> set[TypeVar]:
    return get_type_vars(parse_type(t))


def test_get_type_vars():
    assert help_type_vars("Int") == set()


def test_get_simple_var():
    assert help_type_vars("a") == {TypeVar("a")}


def test_get_simple_refined():
    assert help_type_vars("{x:Int | true}") == set()
    assert help_type_vars("{x:a | true}") == {TypeVar("a")}


def test_get_abstraction():
    assert help_type_vars("(x:Int) -> Bool") == set()
    assert help_type_vars("(x:a) -> Bool") == {TypeVar("a")}
    assert help_type_vars("(x:Bool) -> a") == {TypeVar("a")}
    assert help_type_vars("(x:a) -> a") == {TypeVar("a")}
    assert help_type_vars("(x:a) -> b") == {TypeVar("a"), TypeVar("b")}
    assert help_type_vars("(x:{y:a | true}) -> {z:b | True}") == {
        TypeVar("a"), TypeVar("b")
    }


def test_get_poly():
    assert help_type_vars("forall a:B, (x:a) -> Bool") == set()
    assert help_type_vars("forall a:B, (x:a) -> b") == {TypeVar("b")}


def test_elaboration_foralls():
    t = parse_term("let x : a = 3; x")
    elab_t = elaborate_foralls(t)
    assert isinstance(elab_t, Rec)
    assert elab_t.var_type == TypePolymorphism(name="a",
                                               kind=BaseKind(),
                                               body=TypeVar("a"))


def test_elaboration_foralls2():
    t = parse_term("let x : Int = 3; x")
    elab_t = elaborate_foralls(t)
    assert isinstance(elab_t, Rec)
    assert elab_t.var_type == parse_type("Int")


def test_elaboration_unification():
    t = parse_term(
        "let x : forall a:B, (x:a) -> a = (Λ a:B => (\\x -> x)); let y:Int = x 3; 1"
    )
    v = elaborate_check(EmptyContext(), t, parse_type("Int"))
    v2 = elaborate_remove_unification(EmptyContext(), v)
    expected = parse_term(
        "let x : forall a:B, (x:a) -> a = (Λ a:B => (\\x -> x)); let y:Int = x[{fresh_1:Int| ?k }] 3; 1"
    )
    assert v2 == expected
