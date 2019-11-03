import unittest

from ..frontend import expr, typee
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

    def test_subtyping(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_st(ctx, ty("Boolean"), ty("Boolean"))
        self.assert_st(ctx, ty("Integer"), ty("Integer"))

        self.assert_st(ctx, ty("{x:Integer where true}"), ty("Integer"))
        self.assert_st(ctx, ty("{x:Boolean where x}"), ty("Boolean"))

        self.assert_st(ctx, ty("Boolean"), ty("{x:Boolean where true}"))

        self.assert_st(ctx, ty("{x:Boolean where (5 == 5)}"), ty("Boolean"))

        self.assert_st(ctx, ty("{x:Boolean where (5 == 5)}"),
                       ty("{x:Boolean where (true)}"))
        self.assert_st(ctx, ty("{x:{y:Boolean where true} where (5 == 5)}"),
                       ty("{x:Boolean where true}"))

        self.assert_st(ctx, ty("{x:Integer where (x == 5)}"),
                       ty("{v:Integer where (v > 4)}"))

        self.assert_st(ctx, ty("{x:Integer where (x > 5)}"),
                       ty("{k:Integer where (k > 4)}"))

        self.assert_st(ctx, ty("{x:Integer where (x > 5)}"),
                       ty("{k:Integer where (!(k < 4))}"))

        self.assert_st(ctx, ty("{x:Boolean where x}"),
                       ty("{x:Boolean where true}"))
        self.assert_st(ctx, ty("{x:Boolean where true}"),
                       ty("{x:Boolean where ((x === true) || (x === false))}"))
        self.assert_st(ctx, ty("{y:Boolean where y}"),
                       ty("{x:Boolean where x}"))

        self.assert_st(ctx, ty("{x:{y:Integer where (y < 5)} where (x == 0)}"),
                       ty("{x:Integer where (x==0)}"))

        self.assert_st(ctx, ty("(z:Integer) -> {y:Boolean where y}"),
                       ty("(k:Integer) -> {x:Boolean where x}"))
        self.assert_st(ctx, ty("(a:Integer) -> {b:Integer where (b > 1)}"),
                       ty("(k:Integer) -> {x:Integer where (x > 0)}"))

        self.assert_st(
            ctx,
            ty("(a:{v:Integer where (v > 0) }) -> {b:Integer where (b > 1)}"),
            ty("(k:{z:Integer where (z > 5) }) -> {x:Integer where (x > 0)}"))

        with self.assertRaises(AssertionError):
            self.assert_st(ctx,
                           ty("(a:Integer) -> {r:Integer where (r == a)}"),
                           ty("(a:Integer) -> (b:Integer) -> Bool"))

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


if __name__ == '__main__':
    unittest.main()
