import unittest

from ..types import *
from ..frontend_core import expr, typee
from ..typechecker.unification import unification

ex = expr.parse
ty = typee.parse


class TestTypeUnification(unittest.TestCase):
    def assert_unification(self, ctx, a, b, expected):
        t = ty(expected)
        try:
            r = unification(ctx, ty(a), ty(b))
            self.assertEqual(t, r)
        except TypeException as e:
            self.fail("Cannot unify {} and {}".format(a, b))

    def generic_test(self, a, b, t, extra_ctx=None):
        ctx = TypingContext()
        ctx.setup()
        if extra_ctx:
            for (k, v) in extra_ctx:
                ctx = ctx.with_var(k, ty(v))
        self.assert_unification(ctx, a, b, t)

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
                          "(a:Integer) -> (b:Integer) -> Integer")

    def test_app3(self):
        self.generic_test("(a:Integer) -> (b:Integer) -> Integer",
                          "(K:*) => (a:Integer) -> (b:Integer) -> K",
                          "(a:Integer) -> (b:Integer) -> Integer")
