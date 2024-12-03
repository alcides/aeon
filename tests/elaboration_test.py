from __future__ import annotations

from aeon.core.terms import Rec
from aeon.core.types import BaseKind, BaseType, Top
from aeon.core.types import get_type_vars
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.typechecking.elaboration import elaborate, elaborate_check
from aeon.typechecking.elaboration import elaborate_foralls
from aeon.typechecking.elaboration import elaborate_remove_unification
from aeon.utils.ctx_helpers import build_context
from aeon.prelude.prelude import typing_vars


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
    v = elaborate_check(TypingContext(), t, parse_type("Int"))
    v2 = elaborate_remove_unification(TypingContext(), v)
    expected = parse_term(
        "let x : forall a:B, (x:a) -> a = (Λ a:B => (\\x -> x)); let y:Int = x[Int] 3; 1"
    )
    assert v2 == expected


def test_luhn():
    t = parse_term("(x * 2) > 9")
    ctx = build_context(typing_vars) + VariableBinder("x", BaseType("Int"))

    t2 = elaborate(ctx, t, BaseType("Bool"))

    assert t2.fun.fun.type == BaseType("Int")


def test_bound_type():
    t = parse_term("f 1")
    ctx = TypingContext() + VariableBinder(
        "f", parse_type("forall a:B = Int±Bool, (x:a) -> a"))

    t2 = elaborate(ctx, t, Top())
    assert t2.fun.type == BaseType("Int")
