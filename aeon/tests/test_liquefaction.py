import unittest

from ..frontend_core import expr, typee, kind
from ..types import star, TypingContext, Kind
from ..typechecker.liquefaction import liquefy
from ..typechecker.subtyping import is_subtype
from ..typechecker.type_simplifier import reduce_type

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

        t = reduce_type(self.ctx, ty(ref))
        conv = liquefy(self.ctx, t)
        print("CONV: ", conv, "FROM", ref)
        self.assertEqual(ty(expected), conv)
        #self.assertTrue(is_subtype(self.ctx, conv, ty(expected)) )

    # Literals
    def test_simple(self):
        self.assert_liq('Integer', 'Integer')
        self.assert_liq('{ x:Integer | true }', 'Integer')
        self.assert_liq('{ x:Boolean | x }', '{ x:Boolean | x }')
        self.assert_liq('{ x:Boolean | ((smtEq 1) 2) }',
                        '{ x:Boolean | ((smtEq 1) 2) }')

    def test_minimal(self):
        self.assert_liq(
            '{x:Boolean | not (not true)}',
            'Boolean',
            extra_ctx=[('not', "(a:Boolean) -> {y:Boolean | (smtEq y) (smtNot a)}")]
        )

    def test_middle(self):
        #self.assert_liq('{ x:Boolean | f 1 }',
        #                'Boolean',
        #                extra_ctx=[("f", "(x:Integer) -> Boolean")])
        self.assert_liq(
            '{ x:Boolean | f 1 }',
            '{ x:Boolean | false }',
            extra_ctx=[("f",
                        "(x:Integer) -> { y:Boolean | ((smtEq y) false) }")])

    def test_middle2(self):
        self.assert_liq('{ x:Integer | ((smtEq (f 3)) x) }',
                        '{ x:Integer | ((smtGt x) 3) }',
                        extra_ctx=[
                            ("f",
                             "(k:Integer) -> { y:Integer | ((smtGt y) k) }")
                        ])

    def test_complex(self):
        pass
        #self.assert_liq('{ y:Integer | y == 0 }', '{ y:Integer | ((smtEq y) 0) }')
        #self.assert_liq('{ y:Integer | y == (f 1) }', '{ y:Integer | ((smtEq y) ((smtEq y) 0)) }', extra_ctx=[("f", "(x:Integer) -> { y:Boolean | ((smtEq y) false) }")])
