from __future__ import annotations

from aeon.core.types import Top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.typechecking.typeinfer import check_type


def test_sugar():
    p = parse_program(
        """
    def N.f (i:Int) : Int { 3 }

    def k : (i:Int) -> Int = N.f;

    """, )

    t, ctx, _ = desugar(p)
    x = check_type(ctx, t, Top)
    assert bool(x)
