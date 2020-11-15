import unittest

from aeon.ast import *
from aeon.types import *
from aeon.frontend_core import expr, kind, typee

class TestFrontend(unittest.TestCase):
    def assert_ty(self, typee, expected):
        tee = typee.parse(typee)
        self.assertEqual(tee, expected)

    def assert_ex(self, expression, expected):
        e = expr.parse(expression)
        self.assertEqual(e, expected)

    def assert_kind(self, expression, expected):
        e = kind.parse(expression)
        self.assertEqual(e, expected)

    def test_literals(self):
        self.assert_ex("true", Literal(True, t_b))
        self.assert_ex("false", Literal(False, t_b))
        self.assert_ex("1", Literal(1, t_i))
        self.assert_ex("1.0", Literal(1.0, t_f))

    def test_app(self):
        self.assert_ex("f 1", Application(Var("f"), Literal(True, t_b)))
        self.assert_ex("f a", Application(Var("f"), Var("a")))
        self.assert_ex("f a b", Application(Application(Var("f"), Var("a")), Var("b")))
