import unittest

from ..frontend_core import expr, typee, kind
from ..types import TypingContext, star
from ..typechecker.conversions import *

ex = expr.parse
ty = typee.parse
ki = kind.parse


class TestConversion(unittest.TestCase):
    def test_basic(self):
        for n in ['Integer', 'Boolean', 't']:
            T = ty(n)
            self.assertEqual(type_conversion(T), T)

    def test_refined(self):
        T = ty("{x:Integer where True}")
        self.assertEqual(type_conversion(T), T)

    def test_abs(self):
        T = ty("(x:Integer) -> Boolean")
        self.assertEqual(type_conversion(T), T)

    def test_tabs(self):
        T = ty("(T:*) => Boolean")
        self.assertEqual(type_conversion(T), T)

    def test_tapp(self):
        T = ty("(Integer Boolean)")
        self.assertEqual(type_conversion(T), T)

        T = ty("(((T:*) => Boolean) Integer)")
        self.assertEqual(type_conversion(T), ty("Boolean"))

    def test_beta(self):
        T = ty("(T:*) => Integer")
        self.assertEqual(type_conversion(T), T)

        T = ty("(((T:*) => T) Integer)")
        self.assertEqual(type_conversion(T), ty("Integer"))

        T = ty("(((T:*) => {x:T where true}) Integer)")
        self.assertEqual(type_conversion(T), ty("{x:Integer where true}"))

        T = ty("(((T:*) => (x:T) -> {y:T where true}) Integer)")
        self.assertEqual(type_conversion(T),
                         ty("(x:Integer) -> {y:Integer where true}"))

        T = ty(
            "(((((T1:*) => (T2:*) => (T3:*) => T1) Integer) Boolean) Float)")
        self.assertEqual(type_conversion(T), ty("Integer"))

        T = ty(
            "(((((T1:*) => (T2:*) => (T3:*) => T1) ((T:*) => J)) Boolean) Float)"
        )
        self.assertEqual(type_conversion(T), ty("(T:*) => J"))
