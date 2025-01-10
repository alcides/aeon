from __future__ import annotations

from aeon.core.types import BaseKind
from aeon.elaboration.context import ElaborationTypingContext, build_typing_context
from aeon.sugar.program import SRec
from aeon.sugar.stypes import SBaseType, STypePolymorphism, STypeVar
from aeon.sugar.parser import parse_expression
from aeon.sugar.parser import parse_type

from aeon.elaboration import elaborate, elaborate_check
from aeon.elaboration import elaborate_foralls
from aeon.elaboration import elaborate_remove_unification
from aeon.prelude.prelude import typing_vars


def test_elaboration_foralls():
    t = parse_expression("let x : a = 3; x")
    elab_t = elaborate_foralls(t)
    assert isinstance(elab_t, SRec)
    assert elab_t.var_type == STypePolymorphism(name="a",
                                                kind=BaseKind(),
                                                body=STypeVar("a"))


def test_elaboration_foralls2():
    t = parse_expression("let x : Int = 3; x")
    elab_t = elaborate_foralls(t)
    assert isinstance(elab_t, SRec)
    assert elab_t.var_type == parse_type("Int")


def test_elaboration_unification():
    t = parse_expression(
        "let x : forall a:B, (x:a) -> a = (Λ a:B => (\\x -> x)); let y:Int = x 3; 1"
    )

    v = elaborate_check(ElaborationTypingContext([]), t, parse_type("Int"))
    v2 = elaborate_remove_unification(ElaborationTypingContext([]), v)
    expected = parse_expression(
        "let x : forall a:B, (x:a) -> a = (Λ a:B => (\\x -> x)); let y:Int = x[Int] 3; 1"
    )
    assert v2 == expected


def test_luhn():
    t = parse_expression("(x * 2) > 9")
    ctx = build_typing_context(typing_vars).with_var("x", SBaseType("Int"))
    t2 = elaborate(ctx, t, SBaseType("Bool"))
    assert t2.fun.fun.type == SBaseType("Top")
