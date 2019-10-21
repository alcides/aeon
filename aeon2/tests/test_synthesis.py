import unittest

from ..frontend import expr, typee
from ..synthesis import *
from ..typechecker import *

ex = expr.parse_strict
ty = typee.parse_strict


class TestSynthesis(unittest.TestCase):
    def assert_st(self, ctx, sub, sup):
        if not is_subtype(ctx, sub, sup):
            raise AssertionError(sub, "is not subtype of", sup)

    def assert_synth(self, ctx, t, times=3):
        d = 3
        print("----")
        for i in range(times):
            e = se(ctx, t, d)
            print("Synth'ed: ", e)
            tc(ctx, e, t)
            self.assert_st(ctx, e.type, t)

    def test_synthesis_kind(self):
        ctx = TypingContext()
        ctx.setup()

        self.assertEqual(sk(d=1), star)
        self.assertIn(sk(d=2), [star, Kind(star, star)])
        self.assertIsInstance(sk(d=5), Kind)

    def _test_synthesis(self):

        ctx = TypingContext()
        ctx.setup()
        self.assert_synth(ctx, ty("Boolean"))
        self.assert_synth(ctx, ty("{x:Boolean where x}"))
        self.assert_synth(ctx, ty("{x:Boolean where (x === false)}"))

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
        self.assert_synth(
            ctx,
            ty("(a:{k:Integer where (k > 2)}) -> {v:Integer where (v > 1)}"),
            times=10)


if __name__ == '__main__':
    unittest.main()
