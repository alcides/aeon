from __future__ import annotations

from aeon.core.types import BaseKind
from aeon.core.types import StarKind
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.frontend.parser import parse_type
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.well_formed import wellformed
from aeon.utils.ctx_helpers import built_std_context

empty = EmptyContext()


def test_wf1():
    assert wellformed(empty, t_int)
    assert wellformed(empty, t_bool)
    assert not wellformed(empty, TypeVar("a"))
    assert wellformed(empty.with_typevar("a", BaseKind()), TypeVar("a"))
    assert wellformed(empty.with_typevar("a", StarKind()), TypeVar("a"))


def test_wf2():
    assert wellformed(empty, parse_type("(x:Int) -> Int"))
    assert wellformed(empty, parse_type("(x:Int) -> Bool"))
    assert wellformed(empty, parse_type("(x:Int) -> (y:Bool) -> Bool"))
    assert wellformed(empty, parse_type("(x:((y:Int) -> Bool)) -> (y:Bool) -> Bool"))


def test_refined():
    assert wellformed(empty, parse_type("{x:Int | true}"))
    assert wellformed(empty, parse_type("{x:Int | false}"))
    assert wellformed(empty, parse_type("{x:Bool | x }"))

    assert wellformed(built_std_context(), parse_type("{x:Bool | x == false }"))
    assert wellformed(built_std_context(), parse_type("{x:Int | x > 0}"))


def test_dependent():
    assert wellformed(built_std_context(), parse_type("(y:Int) -> {x:Int | x > y}"))
    assert wellformed(
        VariableBinder(built_std_context(), "x", t_int),
        parse_type("(y:Int) -> {z:Int | x > y}"),
    )


def test_poly():
    assert wellformed(empty, TypePolymorphism("a", BaseKind(), TypeVar("a")))
    assert wellformed(empty, TypePolymorphism("a", StarKind(), TypeVar("a")))
    assert not wellformed(
        empty,
        TypePolymorphism("a", StarKind(), TypeVar("a")),
        BaseKind(),
    )
