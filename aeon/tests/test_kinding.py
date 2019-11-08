import unittest

from ..frontend2 import expr, typee, kind
from ..types import star
from ..typechecker import *

ex = expr.parse_strict
ty = typee.parse_strict
ki = kind.parse_strict


class TestKinding(unittest.TestCase):
    def assert_kind(self, ctx, T, expected_kind):
        k = kinding(ctx, T, expected_kind)
        self.assertEqual(k, expected_kind)

    def assert_not_kind(self, ctx, T, expected_kind):
        self.assertRaises(TypeException, kinding, ctx, T, expected_kind)

    def test_kinding(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_kind(ctx, ty("Integer"), star)
        self.assert_kind(ctx, ty("Boolean"), star)
        self.assert_kind(ctx, ty("Object"), star)

        self.assert_not_kind(ctx, ty("Integer"), Kind(k1=star, k2=star))

        self.assert_kind(ctx, ty("(T:*) => Integer"), Kind(k1=star, k2=star))
        self.assert_kind(ctx, ty("(T:*) => (U:*) => Integer"),
                         Kind(k1=star, k2=Kind(star, star)))

        self.assert_kind(ctx, ty("(T:*) => (U:*) => Integer"),
                         Kind(k1=star, k2=Kind(star, star)))

        self.assert_kind(ctx, ty("(F:*) => F"), Kind(star, star))

        self.assert_kind(
            ctx,
            ty("(HashMap:(* => (* => *))) => (K:*) => (V:*) => ((HashMap K) V)"
               ),
            Kind(k1=Kind(star, Kind(star, star)),
                 k2=Kind(star, Kind(star, star))))
