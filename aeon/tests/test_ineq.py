import unittest

from aeon.synthesis.inequalities import *
from aeon.libraries.stdlib import ty2

from aeon.synthesis.ranges import *
from aeon.types import TypingContext, t_i

from sympy import *
from sympy.solvers.inequalities import *

from aeon.translator import translate

from aeon.typechecker.typing import synth_type
from aeon.typechecker import check_type

name = 'x'

x = Symbol(name)
RangedContext.Variable = name


class TestInequalities(unittest.TestCase):
    def setUp(self):
        # Set the contexts
        self.ctx = TypingContext()
        self.ctx.setup()

    def support_synthesis_with_ineq(self, typee):
        T = ty2(typee)

        self.ctx = self.ctx
        self.ctx.restrictions = list()
        self.ctx.restrictions.append(T.cond)

        expression = Literal(ranged(self.ctx, T.type, T.name, [T.cond]), T)

        print("Type", translate(T), " ~> ", expression)

        print(expression is None)

        self.assertIsNotNone(expression)
        self.assertIsNotNone(check_type(self.ctx, expression, T))

    "Integer"

    def test_ineqs_int_closed_range(self):
        self.support_synthesis_with_ineq(
            '{x:Integer where (x >= 0) && (x <= 10)}')

    def test_ineqs_int_closed_range_with_hole(self):
        self.support_synthesis_with_ineq(
            '{x:Integer where ((x >= 0) && (x <= 10)) && (x != 5)}')

    def test_ineqs_int_even(self):
        self.support_synthesis_with_ineq('{x:Integer where (x % 2) == 0}')

    def test_ineqs_int_odd(self):
        self.support_synthesis_with_ineq('{x:Integer where !((x % 2) == 0)}')

    def test_ineqs_int_with_implies(self):
        self.support_synthesis_with_ineq(
            '{x:Integer where ((x % 2) == 0) --> (x > 0)}')

    def test_ineqs_int_with_lambda(self):
        self.support_synthesis_with_ineq(
            '{x:Integer where (\y:Integer -> x > y)(10)}')

    "Double"

    def test_ineqs_double_not_range(self):
        self.support_synthesis_with_ineq(
            '{x:Double where !((x < 0.0) || (x > 10.0))}')

    def test_ineqs_double_implies_and(self):
        self.support_synthesis_with_ineq(
            '{x:Double where (x > 10.0) --> ((x >= 10.0) && (x <= 20.0))}')

    "Boolean"

    def test_ineqs_bool_true(self):
        self.support_synthesis_with_ineq('{x:Boolean where x == true}')

    def test_ineqs_bool_true_or(self):
        self.support_synthesis_with_ineq('{x:Boolean where x || true}')

    def test_ineqs_bool_not_x(self):
        self.support_synthesis_with_ineq('{x:Boolean where (x || true) --> x}')

    "String"

    def test_ineqs_string_empty(self):
        self.support_synthesis_with_ineq(
            '{x:String where (_String_size(x)) == 0}')

    def test_ineqs_string_non_empty_up_to_10(self):
        self.support_synthesis_with_ineq(
            '{x:String where (_String_size(x)) > 0 && (_String_size(x)) < 10}')

    def test_ineqs_string_even_length(self):
        self.support_synthesis_with_ineq(
            '{x:String where (_String_size(x)) % 2 == 0}')

    # TODO: Consider attributes:

    #ty2('Person'),
    #ty2('{p:Person where (_Person_age(p)) >= 18 --> (_Person_height(p)) > 120}'),
    #ty2('{p:Person where (_Person_size(_Person_name(p))) == 3 }'),
