import unittest

from ..frontend import expr, typee
from ..substitutions import *

ex = expr.parse_strict
ty = typee.parse_strict

t_t = lambda t1, t2, name: substitution_type_in_type(ty(t1), ty(t2), name)
t_v = lambda t1, t2, name: substitution_expr_in_type(ty(t1), ex(t2), name)
t_e = lambda t1, t2, name: substitution_expr_in_expr(ex(t1), ex(t2), name)


class TestSubstitutions(unittest.TestCase):
    def assert_stt(self, original, new, old, expects):
        repl = t_t(original, new, old)
        exp = ty(expects)
        self.assertEqual(repl, exp)

    def assert_svt(self, original, new, old, expects):
        repl = t_v(original, new, old)
        exp = ty(expects)
        self.assertEqual(repl, exp)

    def assert_sve(self, original, new, old, expects):
        repl = t_e(original, new, old)
        exp = ex(expects)
        self.assertEqual(repl, exp)

    def test_type_in_type_basic(self):
        """ type in type, basic_type """

        self.assert_stt("T", "Bool", "T", expects="Bool")
        self.assert_stt("T", "Bool", "X", expects="T")
        self.assert_stt("Bool", "Bool", "X", expects="Bool")
        self.assert_stt("X", "X", "Bool", expects="X")

    def test_type_in_type_refined(self):
        """ type in type, refined """

        self.assert_stt("{x:X where true }",
                        "Boolean",
                        "X",
                        expects="{x:Boolean where true }")
        self.assert_stt("{x:X where true }",
                        "X",
                        "Boolean",
                        expects="{x:X where true }")
        self.assert_stt("{x:{y:X where true} where true }",
                        "Boolean",
                        "X",
                        expects="{x:{y:Boolean where true} where true }")
        self.assert_stt("{x:{y:X where true} where true }",
                        "X",
                        "Boolean",
                        expects="{x:{y:X where true} where true }")

    def test_type_in_type_app(self):
        """ type in type, app """

        self.assert_stt("(x:T) -> T", "X", "T", expects="(x:X) -> X")
        self.assert_stt("(x:T) -> T", "T", "X", expects="(x:T) -> T")
        self.assert_stt("(x:T) -> T", "Bool", "X", expects="(x:T) -> T")

    def test_type_in_type_app_refined(self):
        """ type in type, arrow + refined """

        self.assert_stt("(x:{y: T where true}) -> {z:T where true}",
                        "X",
                        "T",
                        expects="(x:{y: X where true}) -> {z:X where true}")
        self.assert_stt("(x:X) -> {z:T where true}",
                        "X",
                        "T",
                        expects="(x:X) -> {z:X where true}")
        self.assert_stt("(x:X) -> {z:T where true}",
                        "X",
                        "Bool",
                        expects="(x:X) -> {z:T where true}")

    def test_type_in_type_tapp(self):
        """ type in type, tapp """

        self.assert_stt("(List X)", "Bool", "X", expects="(List Bool)")
        self.assert_stt("(List X)", "SList", "List", expects="(SList X)")
        self.assert_stt("(X:(List X)) -> (List X)",
                        "Bool",
                        "X",
                        expects="(X:(List Bool)) -> (List Bool)")
        self.assert_stt("(X:(List X)) -> (List Y)",
                        "Bool",
                        "X",
                        expects="(X:(List Bool)) -> (List Y)")

    def test_type_in_type_tabs(self):
        """ type in type, tabs """
        # TODO: this should not be possible
        self.assert_stt("(X:*) => (List X)",
                        "Y",
                        "X",
                        expects="(X:*) => (List Y)")
        self.assert_stt("(X:*) => {x:Y where true}",
                        "Z",
                        "Y",
                        expects="(X:*) => {x:Z where true}")

    def test_var_in_type(self):
        """ var in type """
        self.assert_svt("Boolean", "1", "x", expects="Boolean")
        self.assert_svt("{x:Boolean where x}",
                        "true",
                        "x",
                        expects="{x:Boolean where true}")
        self.assert_svt("(y:T) -> {x:Boolean where x}",
                        "true",
                        "x",
                        expects="(y:T) -> {x:Boolean where true}")
        self.assert_svt("(T:*) => {x:T where x}",
                        "true",
                        "x",
                        expects="(T:*) => {x:T where true}")

        self.assert_svt("{x:Boolean where (x > 0)}",
                        "1",
                        "x",
                        expects="{x:Boolean where (1 > 0)}")

        self.assert_svt(
            "(a:{x:Boolean where (y > 0)}) -> {z:Boolean where (y > 0)}",
            "1",
            "y",
            expects="(a:{x:Boolean where (1 > 0)}) -> {z:Boolean where (1 > 0)}"
        )

    def test_var_in_expr(self):
        """ var in expr """
        self.assert_sve("x", "1", "x", expects="1")
        self.assert_sve("x", "1", "y", expects="x")
        self.assert_sve("1", "1", "y", expects="1")
        self.assert_sve("[[Integer]]", "1", "y", expects="[[Integer]]")
        self.assert_sve("(1 + 1)", "1", "y", expects="(1 + 1)")
        self.assert_sve("(1 + y)", "2", "y", expects="(1 + 2)")

        self.assert_sve("if a then a else a",
                        "true",
                        "a",
                        expects="if true then true else true")
        self.assert_sve("if a then (b a) else 1",
                        "true",
                        "a",
                        expects="if true then (b true) else 1")

        self.assert_sve("\\a:Integer -> y",
                        "2",
                        "y",
                        expects="\\a:Integer -> 2")
        self.assert_sve("T:* => y", "2", "y", expects="T:* => 2")
        self.assert_sve("y[Boolean]", "2", "y", expects="2[Boolean]")
        self.assert_sve("a b c", "c", "b", expects="a c c")


if __name__ == '__main__':
    unittest.main()
