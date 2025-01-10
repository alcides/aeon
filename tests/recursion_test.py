from __future__ import annotations

from aeon.sugar.stypes import SBaseType
from tests.driver import check_compile


def test_anf():
    source = r"""
        def gcd ( n:Int) (z:Int) : Int {
            if z == 0 then n else (gcd(z)(n % z))
        }

        def main (x:Top) : Int {
            gcd 15 5
        }
"""
    check_compile(source, SBaseType("Top"))
