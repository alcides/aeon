import unittest

from ..frontend_core import expr, typee, kind
from ..types import TypingContext, star
from ..simplification import cnf_simplify
from ..typechecker.type_simplifier import *

ex = expr.parse
ty = typee.parse
ki = kind.parse

conversions = [
    ("! (! a)", "a"),
    ("! (2 > 1)", "(2 <= 1)"),
    ("(a --> b)", "((! a) || b)"),
    ("((a || (b && c)))", "((a || b) && (a || c))"),
    ("((b && c) || a)", "((b || a) && (c || a))"),
    ("((a && (b || c)))", "((a && (b || c)))"),
    ("! (a == b)", "(a != b)"),
    ("! (a != b)", "(a == b)"),
    ("((!a) --> b)", "(a || b)"),
    ("a", "a"),
]


class TestConversion(unittest.TestCase):
    def test_basic(self):
        for (original, expected) in conversions:
            c = cnf_simplify(ex(original))
            self.assertEqual(c, ex(expected))

    def assertSimp(self, t: str, expects: str):
        ctx = TypingContext()
        ctx.setup()
        self.assertEqual(ty(expects), reduce_type(ctx, ty(t)))

    def test_types(self):
        self.assertSimp("((T:*) => T) Integer", "Integer")
        self.assertSimp("Integer & Top", "Integer")
        self.assertSimp("Integer + Top", "Top")
        self.assertSimp("Integer & Bottom", "Bottom")
        self.assertSimp("Integer + Bottom", "Integer")
        self.assertSimp("{x:Integer | true}", "Integer")
        self.assertSimp("{x:{y:Integer | b} | a}",
                        "{x:Integer | ((smtAnd a) b)}")
        self.assertSimp("{x:Integer | true} + {y:Integer | false}", "Integer")
        self.assertSimp("{x:Integer | true} & {y:Integer | false}",
                        "{y:Integer | false}")

    def test_intersections(self):
        self.assertSimp("Integer & Boolean", "Bottom")
        self.assertSimp("Integer & ((T:*) => T)", "Integer")
        self.assertSimp("((T:*) => T) & Integer", "Integer")

    def test_intersections2(self):
        self.assertSimp("((T:*) => (x:T) -> T) & ((K:*) => K)", "((T:*) => (x:T) -> T)")
