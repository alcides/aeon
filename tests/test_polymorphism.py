from aeon.typing.context import EmptyContext, VariableBinder
from typing import Dict

from aeon.typing.typeinfer import check_type
from aeon.frontend.parser import parse_type, parse_term

from aeon.utils.ctx_helpers import build_context
from aeon.typing.typeinfer import sub
from aeon.verification.smt import smt_valid
from aeon.typing.entailment import entailment
from aeon.core.types import t_int


def tt(e: str, t: str, vars: Dict[str, str] = {}):
    ctx = build_context({k: parse_type(v) for (k, v) in vars.items()})
    return check_type(ctx, parse_term(e), parse_type(t))


def test_poly():
    assert tt("let max : Int = 1 in max", "Int")
