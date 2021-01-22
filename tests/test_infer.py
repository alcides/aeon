from typing import Dict

from aeon.typing.typeinfer import check_type
from aeon.frontend.parser import parse_type, parse_term

from aeon.utils.ctx_helpers import build_context


def tt(e: str, t: str, vars: Dict[str, str] = {}):
    ctx = build_context({k: parse_type(v) for (k, v) in vars.items()})
    return check_type(ctx, parse_term(e), parse_type(t))


def test_one_is_int():
    assert tt("1", "Int")
    assert tt("1", "{x:Int|x == 1}")
    assert tt("1", "{x:Int|x > 0}")


def test_true_is_bool():
    assert tt("true", "Bool")
    assert tt("true", "{x:Bool|x == true}")
    assert tt("true", "{x:Bool|x}")


def test_a_is_bool():
    assert tt("a", "Bool", {"a": "Bool"})
    assert tt("a", "Bool", {"a": "{x:Bool| x == true}"})
    assert tt("a", "{x:Bool| x == true}", {"a": "{x:Bool| x == true}"})


def test_abs_is_int():
    # assert tt("\\x -> x", "(x:Int) -> Int")
    assert not tt("\\x -> x", "(x:Bool) -> Int")