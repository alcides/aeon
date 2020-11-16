import unittest

from ..frontend_core import expr, typee, kind
from ..types import TypingContext, star
from ..simplification import cnf_simplify
from ..typechecker.type_simplifier import *

ex = expr.parse
ty = typee.parse
ki = kind.parse

conversions = [
    ("smtGt 2 1", "(smtGt 2) 1"),
    ("smtNot (smtNot a)", "a"),
    ("smtNot (smtGt 2 1)", "(smtLte 2 1)"),
    ("(a --> b)", "(smtOr (smtNot a) b)"),
    ("smtOr a (smtAnd b c)", "smtAnd (smtOr a b) (smtOr a c)"),
    ("smtOr (smtAnd b c) a", "smtAnd (smtOr b a) (smtOr c a)"),
    ("smtAnd a (smtOr b c)", "smtAnd a (smtOr b c)"),
    ("smtNot (smtEq a b)", "(smtIneq a b)"),
    ("smtNot (smtIneq a b)", "(smtEq a b)"),
    ("(smtNot a) --> b", "(smtOr a b)"),
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
        a = ty(expects)
        b = reduce_type(ctx, ty(t))
        self.assertEqual(a, b)

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
        # TODO: The expected type could be even more simplified.
        self.assertSimp("((T:*) => (x:T) -> T) & ((K:*) => K)", "(_fresh_5:*) => (_fresh_4:*) => (_fresh_3:*) => (_fresh_2:*) => ((x:_fresh_2) -> _fresh_3) & ((x:_fresh_4) -> _fresh_5)")
