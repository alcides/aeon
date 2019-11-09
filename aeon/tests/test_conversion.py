import unittest

from ..frontend2 import expr, typee, kind
from ..types import TypingContext, star
from ..typechecker.conversions import *

ex = expr.parse_strict
ty = typee.parse_strict
ki = kind.parse_strict


class TestConversion(unittest.TestCase):
    def test_basic(self):
        for n in ['Integer', 'Boolean', 't']:
            T = ty(n)
            self.assertEquals(type_conversion(T), T)

    def test_refined(self):
        T = ty("{x:Integer where True}")
        self.assertEquals(type_conversion(T), T)

    def test_abs(self):
        T = ty("(x:Integer) -> Boolean")
        self.assertEquals(type_conversion(T), T)

    def test_tabs(self):
        T = ty("(T:*) => Boolean")
        self.assertEquals(type_conversion(T), T)

    def test_tapp(self):
        T = ty("(Integer Boolean)")
        self.assertEquals(type_conversion(T), T)

        T = ty("(((T:*) => Boolean) Integer)")
        self.assertEquals(type_conversion(T), ty("Boolean"))

    def test_beta(self):
        T = ty("(T:*) => Integer")
        self.assertEquals(type_conversion(T), T)

        T = ty("(((T:*) => T) Integer)")
        self.assertEquals(type_conversion(T), ty("Integer"))

        T = ty("(((T:*) => {x:T where true}) Integer)")
        self.assertEquals(type_conversion(T), ty("{x:Integer where true}"))

        T = ty("(((T:*) => (x:T) -> {y:T where true}) Integer)")
        self.assertEquals(type_conversion(T),
                          ty("(x:Integer) -> {y:Integer where true}"))

        T = ty(
            "(((((T1:*) => (T2:*) => (T3:*) => T1) Integer) Boolean) Float)")
        self.assertEquals(type_conversion(T), ty("Integer"))

        T = ty(
            "(((((T1:*) => (T2:*) => (T3:*) => T1) ((T:*) => J)) Boolean) Float)"
        )
        self.assertEquals(type_conversion(T), ty("(T:*) => J"))
