import unittest

from ..frontend_core import expr, typee, kind
from ..types import star, TypingContext, Kind
from ..typechecker.kinding import check_kind
from ..typechecker.exceptions import TypingException

ex = expr.parse
ty = typee.parse
ki = kind.parse


class Testcheck_kind(unittest.TestCase):
    def assert_kind(self, ctx, T, expected_kind):
        k = check_kind(ctx, T, expected_kind)
        self.assertEqual(k, expected_kind)

    def assert_not_kind(self, ctx, T, expected_kind):
        self.assertRaises(TypingException, check_kind, ctx, T, expected_kind)

    def test_check_kind(self):
        ctx = TypingContext()
        ctx.setup()
        self.assert_kind(ctx, ty("Integer"), star)
        self.assert_kind(ctx, ty("Boolean"), star)
        self.assert_kind(ctx, ty("Object"), star)

        self.assert_kind(ctx, ty("{x:Boolean where true}"), star)

        self.assert_kind(ctx, ty("(y:Integer) -> {x:Boolean where true}"),
                         star)

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
