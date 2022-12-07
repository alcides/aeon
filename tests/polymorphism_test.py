from __future__ import annotations

from typing import Dict

from aeon.core.types import t_int
from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.typing.context import EmptyContext
from aeon.typing.context import VariableBinder
from aeon.typing.entailment import entailment
from aeon.typing.typeinfer import check_type
from aeon.typing.typeinfer import sub
from aeon.utils.ctx_helpers import build_context
from aeon.verification.smt import smt_valid


def tt(e: str, t: str, vars: dict[str, str] = {}):
    ctx = build_context({k: parse_type(v) for (k, v) in vars.items()})
    return check_type(ctx, parse_term(e), parse_type(t))


def test_poly():
    assert tt("let max : Int = 1 in max", "Int")
