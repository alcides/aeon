from __future__ import annotations

from aeon.sugar.bind import bind_ectx, bind_sterm
from aeon.core.types import BaseKind
from aeon.elaboration.context import ElaborationTypingContext, build_typing_context
from aeon.sugar.program import SRec
from aeon.sugar.stypes import STypePolymorphism, STypeVar
from aeon.sugar.parser import parse_expression
from aeon.sugar.parser import parse_type

from aeon.elaboration import elaborate, elaborate_check
from aeon.elaboration import elaborate_foralls
from aeon.elaboration import elaborate_remove_unification
from aeon.prelude.prelude import typing_vars
from aeon.utils.name import Name
from aeon.sugar.ast_helpers import st_int, st_bool


def test_elaboration_foralls():
    t = parse_expression("let x : a = 3; x")
    elab_t = elaborate_foralls(t)
    assert isinstance(elab_t, SRec)
    match elab_t.var_type:
        case STypePolymorphism(name=a_name, kind=BaseKind(), body=STypeVar(b_name)):
            assert a_name == b_name
        case _:
            assert False


def test_elaboration_foralls2():
    t = parse_expression("let x : Int = 3; x")
    elab_t = elaborate_foralls(t)
    assert isinstance(elab_t, SRec)
    assert elab_t.var_type == parse_type("Int")


def test_elaboration_unification():
    t = parse_expression("let x : forall a:B, (x:a) -> a = (Λ a:B => (\\x -> x)); let y:Int = x 3; 1")
    ectx = ElaborationTypingContext()
    ectx, subs = bind_ectx(ectx, [])
    t = bind_sterm(t, subs)
    v = elaborate_check(ectx, t, parse_type("Int"))
    v2 = elaborate_remove_unification(ectx, v)
    expected = parse_expression("let x : forall a:B, (x:a) -> a = (Λ a:B => (\\x -> x)); let y:Int = x[Int] 3; 1")
    expected = bind_sterm(expected, subs)
    assert v2 == expected


def test_luhn():
    t = parse_expression("(x * 2) > 9")
    ectx = build_typing_context(typing_vars).with_var(Name("x"), st_int)
    ectx, subs = bind_ectx(ectx, [])
    t = bind_sterm(t, subs)
    t2 = elaborate(ectx, t, st_bool)
    assert t2.fun.fun.type == st_int
