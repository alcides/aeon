from __future__ import annotations

from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.sugar.parser import parse_program
from aeon.prelude.prelude import typing_vars
from aeon.typechecking.elaboration import elaborate
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context

import sys

sys.setrecursionlimit(1500)  # TODO: fix this?


def tt(e: str, t: str, vars: dict[str, str] = {}):
    ctx_vars = {k: parse_type(v) for (k, v) in vars.items()}
    ctx_vars.update(typing_vars)
    ctx = build_context(ctx_vars)
    p = parse_term(e)
    p2 = elaborate(ctx, p)
    exp = parse_type(t)
    return check_type(ctx, p2, exp)


def test_simple_def():
    assert tt("let k : Int = 1 in k", "Int")


def test_poly():
    assert tt(
        """ let max : forall a:B, (x:a) -> (y:a) -> {z:a| (z == x) || (z == y)  } = Λa:B => (\\x -> \\y -> if x < y then y else x) in
            let r = max 0 5 in
            let a : {x:Int | 0 <= x} = r + 1 in
            true""",
        """Top""",
    )


def test_sugar():
    print(parse_program("type List a:*;"))
    assert parse_program("type List a:*;") is None
