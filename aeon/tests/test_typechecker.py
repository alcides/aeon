import unittest

from ..types import *
from ..frontend2 import expr, typee
from ..typechecker import check_type, TypeCheckingError, TypingException

ex = expr.parse_strict
ty = typee.parse_strict


class TestTypeChecking(unittest.TestCase):
    def assert_tc(self, ctx, e, expected):
        t = ty(expected)
        check_type(ctx, ex(e), t)

    def test_basic(self):
        ctx = TypingContext()
        ctx.setup()

        self.assert_tc(ctx, "true", expected="Boolean")
        self.assert_tc(ctx, "false", expected="Boolean")
        self.assert_tc(ctx, "1", expected="{x:Integer where (x == 1)}")
        self.assert_tc(ctx, "11", expected="{x:Integer where (x == 11)}")

    def test_var(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_tc(ctx.with_var("x", ty("Integer")),
                       "x",
                       expected="Integer")
        self.assert_tc(ctx.with_var("x", ty("Integer")),
                       "(x+1)",
                       expected="Integer")

    def test_abs(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_tc(ctx,
                       "\\x:Integer -> 1",
                       expected="(x:Integer) -> Integer")
        self.assert_tc(ctx,
                       "\\x:Integer -> true",
                       expected="(x:Integer) -> Boolean")

    def test_app(self):
        ctx = TypingContext()
        ctx.setup()

        nctx = ctx.with_var("f", ty("(x:Integer) -> Boolean"))
        self.assert_tc(nctx, "f 1", expected="Boolean")

        self.assert_tc(ctx, "(1+1)", expected="Integer")
        self.assert_tc(ctx, "(1+2)", expected="{x:Integer where (x == 3)}")

    def test_divide_by_zero(self):
        ctx = TypingContext()
        ctx.setup()

        self.assert_tc(ctx, "(1 / 3)", expected="Integer")

        with self.assertRaises(TypeCheckingError):
            self.assert_tc(ctx, "(1 / 0)", expected="Integer")

    def test_tabs(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_tc(ctx, "t:* => 1", expected="(t:*) => Integer")

    def test_polymorphism(self):
        ctx = TypingContext()
        ctx.setup()

        self.assert_tc(ctx, "T:* => 1", expected="(T:*) => Integer")
        self.assert_tc(ctx, "(T:* => 1)[Integer]", expected="Integer")

    def test_refined(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_tc(ctx, "false", "{ x:Boolean where (x == false) }")

        self.assert_tc(ctx, "false", "{ x:Boolean where (x == !true) }")

        self.assert_tc(ctx, "1", "{ x:Integer where (x == 1) }")

        self.assert_tc(ctx, "1", "{ x:Integer where (x >= 1) }")

        self.assert_tc(ctx, "1", "{ x:Integer where (x >= 0) }")

        self.assert_tc(ctx, "6", "{ x:Integer where ( (x % 2) == 0) }")

        self.assert_tc(ctx, "1", "{ x:Integer where (x == (2-1)) }")

        with self.assertRaises(TypeCheckingError):
            self.assert_tc(ctx, "1", "{ x:Integer where (x == (3-1)) }")

            self.assert_tc(ctx, "(5 % 0)", "Integer")
            self.assert_tc(ctx, "(5 % 1)", "Integer")

    def test_if(self):
        ctx = TypingContext()
        ctx.setup()

        self.assert_tc(ctx, "if true then 1 else 0",
                       "{ x:Integer where ((x == 1) || (x == 0)) }")

        with self.assertRaises(TypingException) as exc:
            self.assert_tc(ctx, "if true then 1 else 0",
                           "{ x:Integer where ((x == 2) || (x == 0)) }")
        with self.assertRaises(TypingException) as exc:
            self.assert_tc(ctx, "if true then 1 else 0",
                           "{ x:Integer where (x == 0) }")
        with self.assertRaises(TypingException) as exc:
            self.assert_tc(ctx, "if true then 1 else 0",
                           "{ x:Integer where (x == 1) }")


if __name__ == '__main__':
    unittest.main()
