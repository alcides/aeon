from __future__ import annotations

from aeon.sugar.bind import bind_program
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import SVar


def test_parse_decreasing_by_on_definition():
    src = """
        def f (n:Int) : Int decreasing_by [n] = n;
        def main (_:Int) : Int { 0 }
    """
    p = parse_main_program(src, filename="<test>")
    p = bind_program(p, [])
    fdef = p.definitions[0]
    assert len(fdef.decreasing_by) == 1
    assert isinstance(fdef.decreasing_by[0], SVar)
