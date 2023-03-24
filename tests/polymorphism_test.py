from __future__ import annotations

from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context


def tt(e: str, t: str, vars: dict[str, str] = {}):
    ctx = build_context({k: parse_type(v) for (k, v) in vars.items()})
    return check_type(ctx, parse_term(e), parse_type(t))


def test_poly():
    assert tt("let max : Int = 1 in max", "Int")
