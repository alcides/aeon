from __future__ import annotations

from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile


def test_anf_native():
    source = r"""
        def plus1 : (i:Int) -> Int = \i -> i + 1;
        def test_native (i:Int) : Int { native "plus1(x)" }
        def main (i:Int) : Int {  test_native 1}
"""
    check_compile(source, st_top)
