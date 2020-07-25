import unittest

from ..types import *
from ..frontend_core import expr, typee
from ..typechecker import SubtypingException, is_subtype

ex = expr.parse
ty = typee.parse


class TestSubtyping(unittest.TestCase):
    def setUp(self):
        self.ctx = TypingContext()
        self.ctx.setup()

    def assert_st(self, sub, sup, extra_ctx=None):
        ctx = self.ctx
        if extra_ctx:
            for (n, t) in extra_ctx:
                ctx = ctx.with_var(n, ty(t))
        if not is_subtype(ctx, ty(sub), ty(sup)):
            self.fail("{} is not subtype of {}".format(ty(sub), ty(sup)))

    def assert_error(self, sub, sup, extra_ctx=None):
        ctx = self.ctx
        if extra_ctx:
            for (n, t) in extra_ctx:
                ctx = ctx.with_var(n, ty(t))
        try:
            if is_subtype(ctx, ty(sub), ty(sup)):
                self.fail("{} is not subtype of {}".format(ty(sub), ty(sup)))
        except SubtypingException:
            pass

    def test_bottom_top(self):
        self.assert_st("Bottom", "Boolean")
        self.assert_st("Boolean", "Top")
        self.assert_st("Bottom", "Top")

    def test_basic(self):
        self.assert_st("Boolean", "Boolean")
        self.assert_st("Integer", "Integer")

    def test_refined(self):
        self.assert_st("{x:Integer where true}", "Integer")
        self.assert_st("{x:Boolean where x}", "Boolean")
        self.assert_st("Boolean", "{x:Boolean where true}")

    def test_refined_entails(self):

        self.assert_st("{x:Integer where (x == (1+1))}",
                       "{x:Integer where (x == 2)}")

        self.assert_st("{x:Integer where (x == (1+1))}",
                       "{z:Integer where (z == (3-1))}")

        self.assert_st("{x:{y:Boolean where true} where (5 == 5)}",
                       "{x:Boolean where true}")

        self.assert_st("{x:Boolean where true}", "{x:Boolean where true}")
        self.assert_st("{x:Boolean where (5 == 5)}", "Boolean")
        self.assert_st("{x:Boolean where (5 == 5)}", "{x:Boolean where true}")

        self.assert_st("{x:Boolean where (5 == 5)}", "Boolean")
        self.assert_st("{x:Boolean where (5 == 5)}",
                       "{x:Boolean where (true)}")

        self.assert_st("{x:Integer where (x == 5)}",
                       "{v:Integer where (v > 4)}")

        self.assert_st("{x:Integer where (x > 5)}",
                       "{k:Integer where (k > 4)}")

        self.assert_st("{x:Integer where (x > 5)}",
                       "{k:Integer where (!(k < 4))}")

        self.assert_st("{x:{y:Boolean where true} where (5 == 5)}",
                       "{x:Boolean where true}")

        self.assert_st("{x:Boolean where x}", "{x:Boolean where true}")
        self.assert_st("{x:Boolean where true}",
                       "{x:Boolean where ((x == true) || (x == false))}")
        self.assert_st("{y:Boolean where y}", "{x:Boolean where x}")

        self.assert_st("{x:{y:Integer where (y < 5)} where (x == 0)}",
                       "{x:Integer where (x==0)}")

        # Errors
        self.assert_error("{x:Integer where (x > 5)}",
                          "{k:Integer where (k > 6)}")

        self.assert_error("{x:Integer where (x < 5)}",
                          "{k:Integer where (k > (4-6))}")

    def test_abs(self):
        self.assert_st("(z:Integer) -> {y:Boolean where y}",
                       "(k:Integer) -> {x:Boolean where x}")
        self.assert_st("(a:Integer) -> {b:Integer where (b > 1)}",
                       "(k:Integer) -> {x:Integer where (x > 0)}")

        self.assert_st(
            "(a:{v:Integer where (v > 0) }) -> {b:Integer where (b > 1)}",
            "(k:{z:Integer where (z > 5) }) -> {x:Integer where (x > 0)}")

        # Errors
        self.assert_error("(a:Integer) -> {r:Integer where (r == a)}",
                          "(a:Integer) -> (b:Integer) -> Boolean")

    def test_app(self):
        self.assert_st("(((T:*) => T) Integer)", "Integer")
        self.assert_st("Integer", "(((T:*) => T) Integer)")
        self.assert_st("(((T:*) => T) Integer)", "(((T:*) => T) Integer)")
        self.assert_st("(((T:*) => (Y:*) => T) Integer)", "((Z:*) => Integer)")
        self.assert_st("((((T:*) => (Y:*) => T) Integer) Boolean)", "Integer")
        self.assert_st("(T:*) => T", "(T:*) => T")
        self.assert_st("(((T:*) => T) Integer)", "Integer")
        self.assert_st("((((T:*) => ((S:*) => T)) Integer) Void)", "Integer")

        # Errors
        self.assert_error("(((T:*) => T) Integer)", "Boolean")
        self.assert_error("((T:*) => T)", "Boolean")

        self.assert_error("(((T:*) => T) Boolean)", "(((T:*) => T) Integer)")

        self.assert_error("(Integer Boolean)", "(String Double)")
        self.assert_error("Integer", "(String Double)")
        self.assert_error("(String Double)", "Integer")

    def test_bug_synth(self):
        # { c:{ z:Integer where ((!=[??] z) 0) } where ((smtEq c) ((smtPlus a) b)) } ~ { z:Integer where ((!=[??] z) 0) }
        self.assert_st(
            "{ c: { z:Integer where z != 0 } where ((smtEq c) ((smtPlus a) b)) }",
            "{ z:Integer where z != 0 }",
            extra_ctx=[("a", "{ x:Integer | x > 0 }"), ("b", "Integer")])

    def test_union_type(self):
        self.assert_st("Integer", "Integer + Boolean")
        self.assert_st("Boolean", "Integer + Boolean")
        self.assert_st("{x:Boolean | x == true}", "Integer + Boolean")
        self.assert_st("{x:Boolean | x == true}",
                       "{i:Integer | i > 0} + Boolean")
        self.assert_st("{x:Integer | x == 3}", "{i:Integer | i > 0} + Boolean")

        self.assert_st("{x:Integer | x == 3}",
                       "{i:Integer | i > 0} + {j:Integer | j < 0}")
        self.assert_st("{x:Integer | x == (-3)}",
                       "{i:Integer | i > 0} + {j:Integer | j < 0}")
        self.assert_error("{x:Integer | x == 0}",
                          "{i:Integer | i > 0} + {j:Integer | j < 0}")

        self.assert_error("{x:Integer | x == 0}",
                          "{i:Integer | i > 0} + {j:Integer | j < 0}")
        self.assert_st("{x:Integer | x > (-3) && x < 3}",
                       "{i:Integer | i > 0} + {j:Integer | j <= 0}")
