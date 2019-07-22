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
        for i in range(times):
            e = se(ctx, t, d)
            tc(ctx, e, t)
            self.assert_st(ctx, e.type, t)

    def test_synthesis(self):

        ctx = TypingContext()
        ctx.setup()
        self.assert_synth(ctx, ty("Boolean"))
        self.assert_synth(ctx, ty("{x:Boolean where x}"))
        self.assert_synth(ctx, ty("{x:Boolean where (x === false)}"))
        self.assert_synth(ctx, ty("Integer"))
        self.assert_synth(ctx, ty("{x:Integer where (x > 0)}"))
        self.assert_synth(ctx, ty("{x:Integer where ((x % 4) == 0)}"))

        self.assert_synth(ctx, ty("(x:Boolean) -> Integer"))
        self.assert_synth(ctx.with_var("z", ty("(x:Boolean) -> Boolean")),
                          ty("(x:Boolean) -> Boolean"))
        """ TODO
        self.assert_synth(
            ctx.with_var(
                "*",
                tc.
                tc(ctx,
                   n=ty(
                       "(x:Integer) -> (y:Integer) -> {z:Integer where (z == (x*y))}"
                   ))), ty("(x:Integer) -> {y:Integer where (y == (x*2)) }"))
        """


if __name__ == '__main__':
    unittest.main()
