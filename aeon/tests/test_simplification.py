import unittest

from ..frontend_core import expr, typee, kind
from ..types import TypingContext, star
from ..typechecker.conversions import *
from ..simplification import cnf_simplify

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
