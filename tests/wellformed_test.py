from __future__ import annotations

from aeon.core.bind import bind_ctx, bind_type

from aeon.core.types import BaseKind, Kind, Type
from aeon.core.types import StarKind
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.frontend.parser import parse_type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.well_formed import wellformed
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name

empty = TypingContext()


def wf_check(ctx: TypingContext, type: Type, k: Kind = StarKind()) -> bool:
    ctx, subs = bind_ctx(ctx, [])
    type = bind_type(type, subs)
    return wellformed(ctx, type, k=k)


def test_wf1():
    assert wf_check(empty, t_int)
    assert wf_check(empty, t_bool)
    assert not wf_check(empty, TypeVar(Name("a", 0)))
    assert wf_check(empty.with_typevar(Name("a", 0), BaseKind()), TypeVar(Name("a", 0)))
    assert wf_check(empty.with_typevar(Name("a", 0), StarKind()), TypeVar(Name("a", 0)))


def test_wf2():
    assert wf_check(empty, parse_type("(x:Int) -> Int"))
    assert wf_check(empty, parse_type("(x:Int) -> Bool"))
    assert wf_check(empty, parse_type("(x:Int) -> (y:Bool) -> Bool"))
    assert wf_check(empty, parse_type("(x:((y:Int) -> Bool)) -> (y:Bool) -> Bool"))


def test_refined():
    assert wf_check(empty, parse_type("{x:Int | true}"))
    assert wf_check(empty, parse_type("{x:Int | false}"))
    assert wf_check(empty, parse_type("{x:Bool | x }"))

    assert wf_check(built_std_context(), parse_type("{x:Bool | x == false }"))
    assert wf_check(built_std_context(), parse_type("{x:Int | x > 0}"))


def test_dependent():
    assert wf_check(built_std_context(), parse_type("(y:Int) -> {x:Int | x > y}"))
    assert wf_check(
        built_std_context({Name("x", -1): t_int}),
        parse_type("(y:Int) -> {z:Int | x > y}"),
    )


def test_poly():
    a = Name("a", 0)
    assert wf_check(empty, TypePolymorphism(a, BaseKind(), TypeVar(a)))
    assert wf_check(empty, TypePolymorphism(a, StarKind(), TypeVar(a)))
    assert not wf_check(
        empty,
        TypePolymorphism(a, StarKind(), TypeVar(a)),
        BaseKind(),
    )
