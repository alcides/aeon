import unittest

from ..frontend_core import expr, typee, kind
from ..types import star, TypingContext, Kind
from ..typechecker.liquefaction import liquefy
from ..typechecker.subtyping import is_subtype

ex = expr.parse
ty = typee.parse
ki = kind.parse


class TestLiquefaction(unittest.TestCase):
    def setUp(self):
        # Set the contexts
        self.ctx = TypingContext()
        self.ctx.setup()

    def assert_liq(self,
                   ref,
                   expected,
                   extra_ctx=None,
                   extra_uninterpreted=None):
        if extra_ctx:
            for (k, v) in extra_ctx:
                self.ctx = self.ctx.with_var(k, ty(v))
        if extra_uninterpreted:
            for (k, v) in extra_uninterpreted:
                self.ctx = self.ctx.uninterpreted_functions[k] = ty(v)
        conv = liquefy(self.ctx, ty(ref))
        self.assertEqual(ty(expected), conv)
        #self.assertTrue(is_subtype(self.ctx, conv, ty(liq)) )

    # Literals
    def test_simple(self):
        self.assert_liq('Integer', 'Integer')
        self.assert_liq('{ x:Integer | true }', 'Integer')
        self.assert_liq('{ x:Boolean | x }', '{ x:Boolean | x }')
        self.assert_liq('{ x:Boolean | ((smtEq 1) 2) }',
                        '{ x:Boolean | ((smtEq 1) 2) }')

    def test_middle(self):
        self.assert_liq('{ x:Boolean | f 1 }',
                        'Boolean',
                        extra_ctx=[("f", "(x:Integer) -> Boolean")])
        self.assert_liq(
            '{ x:Boolean | f 1 }',
            '{ x:Boolean | ((smtEq x) false) }',
            extra_ctx=[("f",
                        "(x:Integer) -> { y:Boolean | ((smtEq y) false) }")])

    def test_middle2(self):
        self.assert_liq('{ x:Boolean | ((smtGt (f 3)) x) }',
                        '{ x:Boolean | ((smtEq x) false) }',
                        extra_ctx=[
                            ("f",
                             "(x:Integer) -> { y:Integer | ((smtGt y) x) }")
                        ])

    def test_complex(self):
        pass
        #self.assert_liq('{ y:Integer | y == 0 }', '{ y:Integer | ((smtEq y) 0) }')
        #self.assert_liq('{ y:Integer | y == (f 1) }', '{ y:Integer | ((smtEq y) ((smtEq y) 0)) }', extra_ctx=[("f", "(x:Integer) -> { y:Boolean | ((smtEq y) false) }")])
