from __future__ import annotations

from aeon.sugar.parser import parse_type

import sys

from tests.driver import check_compile_expr

sys.setrecursionlimit(1500)  # TODO: fix this?


def tt(e: str, t: str, vars: None | dict[str, str] = None):
    vs = {k: parse_type(v) for (k, v) in vars.items()} if vars is not None else None
    return check_compile_expr(e, parse_type(t), extra_vars=vs)


def test_simple_def():
    assert tt("let k : Int = 1 in k", "Int")


def test_poly():
    assert tt(
        """ let max : forall a:B, (x:a) -> (y:a) -> {z:a| (z == x) || (z == y)  } = Λa:B => (\\x -> \\y -> if x < y then y else x) in
            let r = max 0 5 in
            let a : {m:Int | 0 <= m} = r + 1 in
            true""",
        """Bool""",
    )
