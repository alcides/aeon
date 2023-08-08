from __future__ import annotations

from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.prelude.prelude import typing_vars
from aeon.typechecking.elaboration import elaborate
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context


def tt(e: str, t: str, vars: dict[str, str] = {}):
    ctx_vars = {k: parse_type(v) for (k, v) in vars.items()}
    ctx_vars.update(typing_vars)
    ctx = build_context(ctx_vars)
    p = parse_term(e)
    p2 = elaborate(ctx, p)
    print("got:", p2)
    exp = parse_type(t)
    print("excepted:", exp)
    return check_type(ctx, p2, exp)


def test_simple_def():
    assert tt("let k : Int = 1 in k", "Int")


def test_poly():
    """
    TODO: We're missing the manual/automatic binders at the type and term levels.
    """

    assert tt(
        """ let max : (x:a) -> (y:a) -> a = (\\x -> \\y -> if x < y then y else x) in
            let r = max 0 5 in
            r + 1""",
        """{x:Int| 0 < v}""",
    )
