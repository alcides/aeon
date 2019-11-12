import unittest

from ..frontend2 import expr, typee
from ..typechecker.substitutions import substitution_type_in_type, substitution_expr_in_type, substitution_expr_in_expr,\
     rename_abs, rename_tabs

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
        self.assert_stt("T", "Integer", "T", expects="Integer")

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

    def test_type_in_type_abs(self):
        """ type in type, abs """

        self.assert_stt("(T:*) => S",
                        "Integer",
                        "S",
                        expects="(T:*) => Integer")
        self.assert_stt("(T:*) => (A B)",
                        "Integer",
                        "A",
                        expects="(T:*) => (Integer B)")
        self.assert_stt("(T:*) => (A B)",
                        "Integer",
                        "B",
                        expects="(T:*) => (A Integer)")

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
        self.assert_stt("(x:(List X)) -> (List X)",
                        "Bool",
                        "X",
                        expects="(x:(List Bool)) -> (List Bool)")
        self.assert_stt("(x:(List X)) -> (List Y)",
                        "Bool",
                        "X",
                        expects="(x:(List Bool)) -> (List Y)")

    def test_type_in_type_tabs(self):
        """ type in type, tabs """
        self.assert_stt("(x:*) => (List X)",
                        "Y",
                        "X",
                        expects="(x:*) => (List Y)")
        self.assert_stt("(x:*) => {x:Y where true}",
                        "Z",
                        "Y",
                        expects="(x:*) => {x:Z where true}")

    def test_var_in_type(self):
        """ var in type """
        self.assert_svt("Boolean", "1", "x", expects="Boolean")
        self.assert_svt("{x:Boolean where x}",
                        "true",
                        "x",
                        expects="{x:Boolean where x}")
        self.assert_svt("{y:Boolean where x}",
                        "true",
                        "x",
                        expects="{y:Boolean where true}")
        self.assert_svt("(y:T) -> {x:Boolean where x}",
                        "true",
                        "x",
                        expects="(y:T) -> {x:Boolean where x}")
        self.assert_svt("(y:T) -> {z:Boolean where x}",
                        "true",
                        "x",
                        expects="(y:T) -> {z:Boolean where true}")
        self.assert_svt("(T:*) => {y:T where x}",
                        "true",
                        "x",
                        expects="(T:*) => {y:T where true}")

        self.assert_svt("{k:Boolean where (x > 0)}",
                        "1",
                        "x",
                        expects="{k:Boolean where (1 > 0)}")

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

    def test_substition_with_clashes(self):
        self.assert_sve("\\b:Integer -> (b + a)",
                        "b",
                        "a",
                        expects="\\b_fresh:Integer -> (b_fresh + b)")

    def test_renaming_abs(self):
        self.assertEqual(rename_abs(ex("\\x:Integer -> x"), "y"),
                         ex("\\y:Integer -> y"))
        self.assertEqual(rename_abs(ex("\\x:Integer -> 1"), "y"),
                         ex("\\y:Integer -> 1"))

    def test_renaming_tabs(self):
        self.assertEqual(rename_tabs(ex("t:* => 1[t]"), "v"),
                         ex("v:* => 1[v]"))
        self.assertEqual(rename_tabs(ex("t:* => 1[z]"), "v"),
                         ex("v:* => 1[z]"))


if __name__ == '__main__':
    unittest.main()
