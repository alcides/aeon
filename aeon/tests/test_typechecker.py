import unittest

from ..types import *
from ..frontend2 import expr, typee
from ..typechecker import *

ex = expr.parse_strict
ty = typee.parse_strict


class TestTypeChecking(unittest.TestCase):
    def assert_tc(self, ctx, e, expected):
        t = ty(expected)
        n = tc(ctx, ex(e), t)
        self.assert_st(ctx, n.type, t)

    def assert_st(self, ctx, sub, sup):
        if type(sub) == str:
            sub = ty(sub)
        if type(sup) == str:
            sup = ty(sup)
        if not is_subtype(ctx, sub, sup):
            raise AssertionError(sub, "is not subtype of", sup)

    def test_typechecking(self):

        ctx = TypingContext()
        ctx.setup()

        self.assert_tc(ctx, "true", expected="Boolean")
        self.assert_tc(ctx, "false", expected="Boolean")
        self.assert_tc(ctx, "(1+1)", expected="Integer")

        self.assert_tc(ctx, "1", expected="{x:Integer where (x == 1)}")

        self.assert_tc(ctx, "(1+2)", expected="{x:Integer where (x == 3)}")

        self.assert_tc(ctx.with_var("x", ty("Integer")),
                       "x",
                       expected="Integer")
        self.assert_tc(ctx.with_var("x", ty("Integer")),
                       "(x+1)",
                       expected="Integer")

    def test_divide_by_zero(self):
        ctx = TypingContext()
        ctx.setup()

        self.assert_tc(ctx, "(1 / 3)", expected="Integer")

        with self.assertRaises(TypeException):
            self.assert_tc(ctx, "(1 / 0)", expected="Integer")

    def test_polymorphism(self):
        ctx = TypingContext()
        ctx.setup()

        self.assert_tc(ctx, "T:* => 1", expected="(T:*) => Integer")
        self.assert_tc(ctx, "(T:* => 1)[Integer]", expected="Integer")

        self.assert_st(ctx, "(T:*) => T", "(T:*) => T")
        self.assert_st(ctx, "(((T:*) => T) Integer)", "Integer")

        self.assert_st(ctx, "((((T:*) => ((S:*) => T)) Integer) Void)",
                       "Integer")

    def bug001(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_tc(ctx, "(\\b:Boolean -> !(true))(true)",
                       "{ x:Boolean where (x === false) }")


if __name__ == '__main__':
    unittest.main()
