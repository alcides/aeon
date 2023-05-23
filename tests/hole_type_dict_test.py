from __future__ import annotations

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import BaseType
from aeon.core.types import t_int
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.frontend.parser import parse_type
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.synthesis_grammar.grammar import get_holes_type
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import build_context


def check_hole_type(source, hole_name, expected_type):
    p, ctx, _ = desugar(parse_program(source))
    holes = get_holes_type(ctx, p, top)

    assert holes[hole_name][0] == expected_type


def test_type_int():
    source = r"""
        def test (x:{k:Int | k > 0}) : {z:Int | z < 0} {
        ?r
        }
"""
    check_hole_type(source, "r", t_int)


def test_type_example():
    source = r"""
        type Example;
        def test: Example = ?r ;
"""
    check_hole_type(source, "r", BaseType("Example"))


def test_type_typevar():
    source = r"""
        def test: Int = (?r:Int) + (1:Int) ;
"""
    check_hole_type(source, "r", BaseType("Int"))
