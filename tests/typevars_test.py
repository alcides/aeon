from __future__ import annotations

from aeon.core.types import get_type_vars
from aeon.core.types import TypeVar
from aeon.frontend.parser import parse_type
from aeon.utils.name import Name


def help_type_vars(t: str) -> set[TypeVar]:
    return get_type_vars(parse_type(t))


def test_get_type_vars():
    assert help_type_vars("Int") == set()


def test_get_simple_var():
    assert help_type_vars("a") == {TypeVar(Name("a"))}


def test_get_simple_refined():
    assert help_type_vars("{x:Int | true}") == set()
    assert help_type_vars("{x:a | true}") == {TypeVar(Name("a"))}


def test_get_abstraction():
    assert help_type_vars("(x:Int) -> Bool") == set()
    assert help_type_vars("(x:a) -> Bool") == {TypeVar(Name("a"))}
    assert help_type_vars("(x:Bool) -> a") == {TypeVar(Name("a"))}
    assert help_type_vars("(x:a) -> a") == {TypeVar(Name("a"))}
    assert help_type_vars("(x:a) -> b") == {TypeVar(Name("a")), TypeVar(Name("b"))}
    assert help_type_vars("(x:{y:a | true}) -> {z:b | True}") == {TypeVar(Name("a")), TypeVar(Name("b"))}


def test_get_poly():
    assert help_type_vars("forall a:B, (x:a) -> Bool") == set()
    assert help_type_vars("forall a:B, (x:a) -> b") == {TypeVar(Name("b"))}
