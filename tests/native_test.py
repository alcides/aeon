from __future__ import annotations

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import t_int
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context


def check_compile(source, ty):
    p, ctx, ectx = desugar(parse_program(source))
    assert check_type(ctx, p, ty)
    assert eval(p, ectx) == 2


def test_anf():
    source = r"""
        type Unit;
        def plus1 : (i:Int) -> Int = \i -> i + 1;
        def test_native : (i:Int) -> Int = native "lambda x: plus1(x)";
        def main (i:Int) : Int {  test_native 1}
"""
    check_compile(source, top)
