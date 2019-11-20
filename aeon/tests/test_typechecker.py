import unittest

from ..types import *
from ..frontend2 import expr, typee
from ..typechecker import check_type, TypeCheckingError, TypingException, synth_type

ex = expr.parse_strict
ty = typee.parse_strict


class TestTypeChecking(unittest.TestCase):
    def assert_tc(self, ctx, e, expected):
        t = ty(expected)
        check_type(ctx, ex(e), t)

    def generic_test(self, e, t, extra_ctx=None):
        ctx = TypingContext()
        ctx.setup()
        if extra_ctx:
            for (k, v) in extra_ctx:
                ctx = ctx.with_var(k, ty(v))
        self.assert_tc(ctx, e, t)

    def test_basic_true(self):
        self.generic_test("true", "Boolean")

    def test_basic_false(self):
        self.generic_test("false", "Boolean")

    def test_basic_1(self):
        self.generic_test("1", "{x:Integer where (x == 1)}")

    def test_basic_11(self):
        self.generic_test("11", "{x:Integer where (x == 11)}")

    def test_var_1(self):
        self.generic_test("x", "Integer", extra_ctx=[("x", "Integer")])

    def test_var_2(self):
        self.generic_test("(x+1)", "Integer", extra_ctx=[("x", "Integer")])

    def test_abs_1(self):
        self.generic_test("\\x:Integer -> 1", "(x:Integer) -> Integer")

    def test_abs_2(self):
        self.generic_test("\\x:Integer -> true", "(x:Integer) -> Boolean")

    def test_app_1(self):
        self.generic_test("f 1",
                          "Boolean",
                          extra_ctx=[("f", "(x:Integer) -> Boolean")])

    def test_app_plus1(self):
        self.generic_test("(1+1)", "Integer")

    def test_app_plus2(self):
        self.generic_test("(1+2)", "{x:Integer where (x == 3)}")

    def test_divide(self):
        self.generic_test("(1/3)", "Integer")

    def test_divide_by_zero(self):
        with self.assertRaises(TypeCheckingError):
            self.generic_test("(1/0)", "Integer")

    def test_tabs(self):
        self.generic_test("t:* => 1", "(t:*) => Integer")

    def test_polymorphism_1(self):
        self.generic_test("(T:* => 1)[Integer]", "Integer")

    def test_refined_1(self):
        self.generic_test("false", "{ x:Boolean where (x == false) }")

    def test_refined_2(self):
        self.generic_test("false", "{ x:Boolean where (x == !true) }")

    def test_refined_3(self):
        self.generic_test("1", "{ x:Integer where (x == 1) }")

    def test_refined_4(self):
        self.generic_test("1", "{ x:Integer where (x >= 1) }")

    def test_refined_5(self):
        self.generic_test("1", "{ x:Integer where (x >= 0) }")

    def test_refined_6(self):
        self.generic_test("6", "{ x:Integer where ( (x % 2) == 0) }")

    def test_refined_7(self):
        self.generic_test("1", "{ x:Integer where (x == (2-1)) }")

    def test_refined_8(self):
        self.generic_test("(1 + 1)", "{ x:Integer where (x == 2) }")

    def test_refined_9(self):
        self.generic_test("(1 - 1)", "{ x:Integer where (x == 0) }")

    def test_refined_10(self):
        self.generic_test("(true && false)",
                          "{ x:Boolean where (x == false) }")

    def test_refined_11(self):
        self.generic_test("(5 % 1)", "Integer")

    def test_refined_12(self):
        with self.assertRaises(TypeCheckingError):
            self.generic_test("1", "{ x:Integer where (x == (3-1)) }")

    def test_refined_13(self):
        with self.assertRaises(TypeCheckingError):
            self.generic_test("(5 % 0)", "Integer")

    def test_if_1(self):
        self.generic_test("if true then 1 else 0",
                          "{ x:Integer where ((x == 1) || (x == 0)) }")

    def test_if_2(self):
        with self.assertRaises(TypingException):
            self.generic_test("if true then 1 else 0",
                              "{ x:Integer where ((x == 2) || (x == 0)) }")

    def test_if_3(self):
        with self.assertRaises(TypingException):
            self.generic_test("if true then 1 else 0",
                              "{ x:Integer where (x == 0) }")

    def test_if_4(self):
        self.generic_test("if true then 1 else 0",
                          "{ x:Integer where (x == 1) }")

    def test_if_5(self):
        self.generic_test(
            "(if false then ((\\u:Integer -> u) 9) else (if true then 3 else 1))",
            "{ x:Integer where (x == 3) }")

    def test_abs(self):
        self.generic_test("((\\u:Integer -> u) 9)",
                          "{ x:Integer where (x == 9) }")


if __name__ == '__main__':
    unittest.main()
