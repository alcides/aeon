import unittest

from ..frontend_core import expr, typee, kind
from ..types import star, TypingContext, Kind
from ..typechecker.kinding import check_kind
from ..typechecker.exceptions import TypingException

ex = expr.parse
ty = typee.parse
ki = kind.parse


class Testcheck_kind(unittest.TestCase):    
    def setUp(self):
        # Set the contexts
        self.ctx = TypingContext()
        self.ctx.setup()
    
    def add_extra_T(self, extra_T):
        ctx = self.ctx
        if extra_T:
            for name, kind in extra_T:
                ctx = ctx.with_type_var(name, kind)
        return ctx

    def assert_kind(self, T, expected_kind, extra_T=None):
        ctx = self.add_extra_T(extra_T)
        k = check_kind(ctx, T, expected_kind)
        self.assertEqual(k, expected_kind)

    def assert_not_kind(self, T, expected_kind, extra_T=None):
        ctx = self.add_extra_T(extra_T)
        self.assertRaises(TypingException, check_kind, ctx, T, expected_kind)

    def test_check_native_kind(self):
        self.assert_kind(ty("Integer"), star)
        self.assert_kind(ty("Boolean"), star)
        self.assert_kind(ty("Double"), star)
        self.assert_kind(ty("String"), star)
        self.assert_kind(ty("Object"), star)
        self.assert_kind(ty("Bottom"), star)
        self.assert_kind(ty("Top"), star)

        self.assert_not_kind(ty("Integer"), Kind(k1=star, k2=star))

    def test_check_where_kind(self):
        self.assert_kind(ty("{x:Boolean where true}"), star)
        
        self.assert_kind(ty("{x:(T:*) => Boolean where true}"), Kind(k1=star,
                         k2=star))

        self.assert_kind(ty("{x:List where (List_size x) == 0}"), Kind(k1=star,
                         k2=star), extra_T=[('List', Kind(star, star))])
        self.assert_kind(ty("{x:(List Integer) where (List_size x) == 0}"),
                         star, extra_T=[('List', Kind(star, star))])

    def test_check_abs_kind(self):
        self.assert_kind(ty("(y:Integer) -> {x:Boolean where true}"),
                         star)

    def test_check_tabs_kind(self):
        self.assert_kind(ty("(T:*) => Integer"), Kind(k1=star, k2=star))
        self.assert_kind(ty("(T:*) => (U:*) => Integer"),
                         Kind(k1=star, k2=Kind(star, star)))

        self.assert_kind(ty("(F:*) => F"), Kind(star, star))

        self.assert_kind(
            ty("(HashMap:(* => (* => *))) => (K:*) => (V:*) => ((HashMap K) V)"
               ),
            Kind(k1=Kind(star, Kind(star, star)),
                 k2=Kind(star, Kind(star, star))))
