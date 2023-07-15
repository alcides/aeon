from __future__ import annotations

from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context


def tt(e: str, t: str, vars: dict[str, str] = {}):
    ctx = build_context({k: parse_type(v) for (k, v) in vars.items()})
    return check_type(ctx, parse_term(e), parse_type(t))


def test_simple_def():
    assert tt("let max : Int = 1 in max", "Int")


def test_poly():
    """
    TODO: We're missing the manual/automatic binders at the type and term levels.
    """

    print(
        parse_term(
            """
let max : (x:a) -> (y:a) -> a = (\\x -> \\y -> if x < y then y else x) in
             let r = max[int] 0 5 in
              r + 1

              """,
        ),
    )

    assert tt(
        """
let max : (x:a) -> (y:a) -> a = (\\x -> \\y -> if x < y then y else x) in
             let r = max 0 5 in
              r + 1

              """,
        """{x:Int| 0 < v}""",
    )
