import unittest
import random

from ..types import TypingContext, Kind, star
from ..frontend2 import expr, typee
from ..synthesis import WeightManager, sk, se, se_bool, se_int, se_var, se_app, \
    se_where, stax
from ..typechecker import check_type, is_subtype

ex = expr.parse_strict
ty = typee.parse_strict


class TestSynthesis(unittest.TestCase):
    def setUp(self):
        random.seed(10)

    def assert_st(self, ctx, sub, sup):
        if not is_subtype(ctx, sub, sup):
            raise AssertionError(sub, "is not subtype of", sup)

    def assert_synth(self, ctx, t, times=3, fun=se):
        d = 3
        print("----")
        for i in range(times):
            e = fun(ctx, t, d)
            print(t, "~>", e)
            check_type(ctx, e, t)
            self.assert_st(ctx, e.type, t)

    def test_synthesis_kind(self):
        ctx = TypingContext()
        ctx.setup()

        self.assertEqual(sk(0), star)
        self.assertIn(sk(2), [star, Kind(star, star)])
        self.assertIsInstance(sk(5), Kind)

    def test_synthesis_step_by_step(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_synth(ctx, ty("Boolean"), fun=se_bool)

        self.assert_synth(ctx, ty("Integer"), fun=se_int)
        self.assert_synth(ctx.with_var("x", ty("Boolean")),
                          ty("Boolean"),
                          fun=se_var)
        self.assert_synth(ctx.with_var("x", ty("Integer")),
                          ty("Integer"),
                          fun=se_var)

        self.assert_synth(ctx.with_var("x", ty("{x:Integer where (x > 3)}")),
                          ty("Integer"),
                          fun=se_var)
        self.assert_synth(ctx, ty("Integer"), fun=se_int)

        self.assert_synth(ctx.with_var("x", ty("{x:Integer where (x > 3)}")),
                          ty("{y:Integer where (y > 2)}"),
                          fun=se_var)
        self.assert_synth(ctx, ty("{y:Integer where (y > 2)}"), fun=se_where)

    def test_synthesis(self):

        ctx = TypingContext()
        ctx.setup()
        self.assert_synth(ctx, ty("Boolean"))
        self.assert_synth(ctx, ty("{x:Boolean where x}"))
        self.assert_synth(ctx, ty("{x:Boolean where (x == false)}"))

        self.assert_synth(ctx, ty("Integer"))
        self.assert_synth(ctx, ty("{x:Integer where (x > 0)}"))
        self.assert_synth(ctx, ty("{x:Integer where ((x % 4) == 0)}"))

        self.assert_synth(ctx,
                          ty("{x:Integer where (((x % 4) == 0) && (x > 2))}"))

        self.assert_synth(ctx, ty("(x:Boolean) -> Integer"))
        self.assert_synth(ctx.with_var("z", ty("(x:Boolean) -> Boolean")),
                          ty("(x:Boolean) -> Boolean"))

        self.assert_synth(ctx.with_var("z", ty("{k:Integer where (k > 0)}")),
                          ty("{v:Integer where (v > 1)}"))

    def test_synthesis_current(self):
        ctx = TypingContext()
        ctx.setup()

        self.assert_synth(ctx, ty("{x:Integer where (x > 0)}"))

        self.assert_synth(
            ctx,
            ty("(a:{k:Integer where (k > 2)}) -> {v:Integer where (v > 1)}"),
            times=10)

        self.assert_synth(ctx,
                          ty("(a:Integer) -> {v:Integer where (v > 1)}"),
                          times=10)

    def assert_stax(self, ctx, e, x, T):
        NT = stax(ctx, e, x, T, 1)
        #print("NT:", NT)
        assert (is_subtype(ctx, NT, T))

    def test_stax(self):
        ctx = TypingContext()
        ctx.setup()

        T = ty("{v:Integer where (v == 1)}")
        self.assert_stax(ctx.with_var("x", T), expr.parse_strict("1"), "x", T)

        T = ty("(v:{a:Integer where (a > 1)}) -> {k:Boolean where (k)}")
        self.assert_stax(ctx.with_var("x", ty("{x:Integer where (x==1)}")),
                         expr.parse_strict("1"), "x", T)


if __name__ == '__main__':
    unittest.main()
