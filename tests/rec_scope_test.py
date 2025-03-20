from __future__ import annotations

from aeon.sugar.stypes import SBaseType
from tests.driver import check_compile


def test_rec_scope():
    source = r"""
        def assert (b:{b:Bool | b}) : Unit { native "()" }
        def main (args:Int) : Int {
            b = 3;
            1
        }
"""
    check_compile(source, SBaseType("Top"), 1)
