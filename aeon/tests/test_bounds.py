import unittest

from ..frontend_core import expr, typee, kind
from ..types import TypingContext, star, top, bottom
from ..typechecker.bounds import glb, lub

ex = expr.parse
ty = typee.parse
ki = kind.parse


class TestLUB(unittest.TestCase):
    def assert_lub(self, T, U, expected):
        self.assertEqual(lub(ty(T), ty(U)), ty(expected))

    def test_lub_basic(self):
        self.assert_lub("Integer", "Boolean", expected="Top")
        self.assert_lub("Integer", "Integer", expected="Integer")
        self.assert_lub("Integer", "Top", expected="Integer")
        self.assert_lub("Top", "Integer", expected="Integer")
        self.assert_lub("Integer", "Bottom", expected="Bottom")
        self.assert_lub("Bottom", "Integer", expected="Bottom")

    def test_lub_where(self):
        self.assert_lub("Integer",
                        "{x:Integer where (x>0)}",
                        expected="Integer")
        self.assert_lub("{x:Integer where (x>0)}",
                        "Integer",
                        expected="Integer")
        self.assert_lub("{x:Integer where (x>0)}",
                        "{x:Integer where (x<0)}",
                        expected="{x:Integer where ((x>0) || (x<0))}")
        self.assert_lub("Bottom", "{x:Integer where (x>0)}", expected="Bottom")
        self.assert_lub("{x:Integer where (x>0)}", "Bottom", expected="Bottom")
        self.assert_lub("Top",
                        "{x:Integer where (x>0)}",
                        expected="{x:Integer where (x>0)}")
        self.assert_lub("{x:Integer where (x>0)}",
                        "Top",
                        expected="{x:Integer where (x>0)}")

    def test_lub_abs(self):
        self.assert_lub("(x:Boolean) -> Integer",
                        "(x:Boolean) -> Integer",
                        expected="(x:Boolean) -> Integer")
        self.assert_lub("(x:Integer) -> Integer",
                        "(x:Boolean) -> Integer",
                        expected="(x:Bottom) -> Integer")
        self.assert_lub("(x:Boolean) -> Integer",
                        "(x:Boolean) -> Boolean",
                        expected="(x:Boolean) -> Top")
        self.assert_lub("(x:Integer) -> Integer",
                        "(x:Boolean) -> Boolean",
                        expected="(x:Bottom) -> Top")

    def test_lub_tabs(self):
        self.assert_lub("(T:*) => Integer",
                        "(T:*) => Integer",
                        expected="(T:*) => Integer")
        self.assert_lub("(T:*) => Integer",
                        "(T:*) => Boolean",
                        expected="(T:*) => Top")
        self.assert_lub("(T:*) => {x:Integer where (x>0)}",
                        "(T:*) => Integer",
                        expected="(T:*) => Integer")


class TestGLS(unittest.TestCase):
    def assert_glb(self, T, U, expected):
        self.assertEqual(glb(ty(T), ty(U)), ty(expected))

    def test_glb_basic(self):
        self.assert_glb("Integer", "Boolean", expected="Bottom")
        self.assert_glb("Integer", "Integer", expected="Integer")
        self.assert_glb("Integer", "Bottom", expected="Integer")
        self.assert_glb("Bottom", "Integer", expected="Integer")
        self.assert_glb("Integer", "Top", expected="Top")
        self.assert_glb("Top", "Integer", expected="Top")

    def test_glb_where(self):
        self.assert_glb("Integer",
                        "{x:Integer where (x>0)}",
                        expected="{x:Integer where (x>0)}")
        self.assert_glb("{x:Integer where (x>0)}",
                        "Integer",
                        expected="{x:Integer where (x>0)}")
        self.assert_glb("{x:Integer where (x>0)}",
                        "{x:Integer where (x<0)}",
                        expected="{x:Integer where ((x>0) && (x<0))}")
        self.assert_glb("Bottom",
                        "{x:Integer where (x>0)}",
                        expected="{x:Integer where (x>0)}")
        self.assert_glb("{x:Integer where (x>0)}",
                        "Bottom",
                        expected="{x:Integer where (x>0)}")
        self.assert_glb("Top", "{x:Integer where (x>0)}", expected="Top")
        self.assert_glb("{x:Integer where (x>0)}", "Top", expected="Top")

    def test_glb_abs(self):
        self.assert_glb("(x:Boolean) -> Integer",
                        "(x:Boolean) -> Integer",
                        expected="(x:Boolean) -> Integer")
        self.assert_glb("(x:Integer) -> Integer",
                        "(x:Boolean) -> Integer",
                        expected="(x:Top) -> Integer")
        self.assert_glb("(x:Boolean) -> Integer",
                        "(x:Boolean) -> Boolean",
                        expected="(x:Boolean) -> Bottom")
        self.assert_glb("(x:Integer) -> Integer",
                        "(x:Boolean) -> Boolean",
                        expected="(x:Top) -> Bottom")

    def test_glb_tabs(self):
        self.assert_glb("(T:*) => Integer",
                        "(T:*) => Integer",
                        expected="(T:*) => Integer")
        self.assert_glb("(T:*) => Integer",
                        "(T:*) => Boolean",
                        expected="(T:*) => Bottom")
        self.assert_glb("(T:*) => {x:Integer where (x>0)}",
                        "(T:*) => Integer",
                        expected="(T:*) => {x:Integer where (x>0)}")
