import unittest

from ..types import *
from ..frontend_core import expr, typee
from ..typechecker.unification import unification
from ..typechecker.type_simplifier import reduce_type

ex = expr.parse
ty = typee.parse


class TestTypeUnification(unittest.TestCase):
    def assert_unification(self, ctx, a, b, expected):
        t = ty(expected)
        try:
            r = unification(ctx, ty(a), ty(b))
            rr = reduce_type(ctx, r)
            tr = reduce_type(ctx, t)

            self.assertEqual(tr, rr)
        except TypeException as e:
            self.fail("Cannot unify {} and {}".format(a, b))

    def generic_test(self, a, b, t, extra_ctx=None):
        ctx = TypingContext()
        ctx.setup()
        if extra_ctx:
            for (k, v) in extra_ctx:
                ctx = ctx.with_var(k, ty(v))
        self.assert_unification(ctx, a, b, t)

    def assert_type_delegate(self, a, b, expected, extra_ctx=None):
        ctx = TypingContext()
        ctx.setup()
        if extra_ctx:
            for (k, v) in extra_ctx:
                ctx = ctx.with_var(k, ty(v))
        t = ty(expected)
        r = unification(ctx, ty(a), ty(b))
        self.assertIsInstance(r, TypeApplication)
        self.assertEqual(t, r.argument)


    def test_basic_true(self):
        self.generic_test("Boolean", "Boolean", "Boolean")

    def test_tabs(self):
        self.generic_test("Boolean", "(T:*) => T", "Boolean")

    def test_tabs_2(self):
        self.generic_test("List Boolean", "(T:*) => List T", "List Boolean")

    def test_tabs_3(self):
        self.generic_test("Map Integer Boolean", "(T:*) => (K:*) => Map T K",
                          "Map Integer Boolean")

    def test_app(self):
        self.generic_test("(a:Integer) -> (b:Integer) -> Integer",
                          "(T:*) => (a:T) -> (b:T) -> T",
                          "(a:Integer) -> (b:Integer) -> Integer")

    def test_app2(self):
        self.generic_test("(T:*) => (a:T) -> (b:T) -> T",
                          "(K:*) => (a:Integer) -> (b:Integer) -> K",
                          "((T:*) => (a:T) -> (b:T) -> T) Top")

    def test_app3(self):
        self.generic_test("(a:Integer) -> (b:Integer) -> Integer",
                          "(K:*) => (a:Integer) -> (b:Integer) -> K",
                          "(a:Integer) -> (b:Integer) -> Integer")
    def test_app4(self):
        self.generic_test("(a:Integer) -> (b:Integer) -> Integer",
                          "(K:*) => (a:Integer) -> (b:K) -> K",
                          "(a:Integer) -> (b:Integer) -> Integer")
    def test_app5(self):
        self.generic_test("(a:Integer) -> (b:Integer) -> Integer",
                          "(K:*) => (a:K) -> (b:K) -> K",
                          "(a:Integer) -> (b:Integer) -> Integer")
    def test_app6(self):
        self.generic_test("(T:*) => (a:T) -> (b:Integer) -> Integer",
                          "(K:*) => (a:K) -> (b:K) -> K",
                          "((T:*) => (a:T) -> (b:Integer) -> Integer) Top")

    def test_app7(self):
        self.generic_test("(T:*) => {x:T | true}",
                          "{x:Integer | true}",
                          "Integer")

    def test_app8(self):
        self.generic_test("{x:Integer | true}",
                          "(T:*) => {x:T | true}",
                          "Integer")

    def test_check(self):
        mais = "(T :*) => (a:T) -> (b:T) -> {z:T | where (smtEq c) ((smtPlus a) b) }"
        site = "(a1: {x : Integer | x == 1}) -> (a2: {y : Integer | y == 2}) -> {z:Integer | z == 3}"
        self.assert_type_delegate( mais, site, "Integer" )

