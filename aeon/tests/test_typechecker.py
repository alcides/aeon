import unittest

from ..types import TypingContext
from ..frontend_core import expr, typee
from ..typechecker.uinference import check_type, TypeCheckingError

ex = expr.parse
ty = typee.parse


class TestTypeChecking(unittest.TestCase):
    def assert_tc(self, ctx, e, expected, should_fail=False):
        t = ty(expected)
        type_ok = check_type(ctx, ex(e), t)
        if should_fail:
            self.assertFalse(type_ok)
        else:
            self.assertTrue(type_ok)

    def generic_test(self, e, t, extra_ctx=None, should_fail=False):
        ctx = TypingContext()
        ctx.setup()
        if extra_ctx:
            for (k, v) in extra_ctx:
                ctx = ctx.with_var(k, ty(v))
        self.assert_tc(ctx, e, t, should_fail)

    def test_basic_true(self):
        self.generic_test("true", "Boolean")

    def test_basic_false(self):
        self.generic_test("false", "Boolean")

    def test_basic_1(self):
        self.generic_test("1", "{x:Integer | (x == 1)}")

    def test_basic_negative(self):
        self.generic_test("-2", "{x:Integer | x == (-2)}")

    def test_basic_11(self):
        self.generic_test("11", "{x:Integer | (x == 11)}")

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
        self.generic_test("(1+2)", "{x:Integer | (x == 3)}")

    def test_divide(self):
        self.generic_test("(1/3)", "Integer")

    def test_true_or_true(self):
        self.generic_test("true || true", "Boolean")
        self.generic_test("true && true", "Boolean")

    def test_divide_by_zero(self):
        self.generic_test("(1/0)", "Integer", should_fail=True)

    def test_tabs(self):
        self.generic_test("\\t:* => 1", "(t:*) => Integer")

    def test_polymorphism_1(self):
        self.generic_test("(\\T:* => 1)[Integer]", "Integer")

    def test_refined_1(self):
        self.generic_test("false", "{ x:Boolean | (x == false) }")

    def test_refined_2(self):
        self.generic_test("false", "{ x:Boolean | (x == (!true)) }")

    def test_refined_3(self):
        self.generic_test("1", "{ x:Integer | (x == 1) }")

    def test_refined_4(self):
        self.generic_test("1", "{ x:Integer | (x >= 1) }")

    def test_refined_5(self):
        self.generic_test("1", "{ x:Integer | (x >= 0) }")

    def test_refined_6(self):
        self.generic_test("6", "{ x:Integer | ( (x % 2) == 0) }")

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
        self.generic_test("1",
                          "{ x:Integer where (x == (3-1)) }",
                          should_fail=True)

    def test_refined_13(self):
        self.generic_test("(5 % 0)", "Integer", should_fail=True)

    def test_refined_14(self):
        self.generic_test("5",
                          "{x:Integer where ((\\y:Integer -> x > y) 10)}",
                          should_fail=True)

    def test_refined_15(self):
        self.generic_test('5.0',
                          '{x:Double where true}',
                          extra_ctx=[("intToDouble", "(x:Integer) -> Double")])

    def test_refined_string_simple(self):
        self.generic_test("\"abc\"", "String")

    def test_refined_string_refined(self):
        self.generic_test("\"abc\"", "{x:String | (String_size x) >= 0 }")

    def test_refined_string_empty(self):
        self.generic_test("\"\"", "{y:String | (String_size y) == 0 }")

    def test_refined_string_3(self):
        self.generic_test("\"abc\"", "{x:String | (String_size x) == 3 }")

    def test_refined_string_wrong_size(self):
        self.generic_test("\"ac\"",
                          "{x:String | (String_size x) == 3 }",
                          should_fail=True)

    def test_if_1(self):
        self.generic_test("if true then 1 else 0",
                          "{ x:Integer where ((x == 1) || (x == 0)) }")

    def test_abs_wrong(self):
        self.generic_test("((\\u:Integer -> u) 9)",
                          "{ x:Integer where (x == 9) }",
                          should_fail=True)

    def test_complex(self):
        self.generic_test("f 5",
                          "{ x:Boolean | (x == true) }",
                          extra_ctx=[
                              ("f",
                               "(x:Integer) -> { b:Boolean | b ==(x > 3) }")
                          ])

    def test_weird_case(self):
        self.generic_test("-465503093806808577", "{z:Integer | (z != 0)}")

    def test_union(self):
        self.generic_test("1", "Integer + Boolean")

    def test_union2(self):
        self.generic_test("1", "Integer & {x:Integer | x < 4}")

    def test_exists(self):
        self.generic_test(
            "1",
            "{x:Integer | smtExists( \y:{z:Integer | z == 2} -> (x+1 == y) ) }"
        )

    def test_from_synth(self):
        self.generic_test("6724078025571563077", "{z:Integer | (z != 0)}")


if __name__ == '__main__':
    unittest.main()
