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


class TestRanged(unittest.TestCase):
    def setUp(self):
        # Set the contexts
        self.ctx = TypingContext()
        self.ctx.setup()

    def support_synthesis_with_ineq(self, typee):
        T = ty2(typee)
        value = try_ranged(self.ctx, T)
        self.assertIsNotNone(value)
        e = Literal(value, T)
        self.assertIsNotNone(check_type(self.ctx, e, T))

    "Integer"

    def test_ranged_int_closed_range(self):
        self.support_synthesis_with_ineq(
            '{x:Integer where (x >= 0) && (x <= 10)}')

    def test_ranged_int_closed_range_with_hole(self):
        self.support_synthesis_with_ineq(
            '{x:Integer where ((x >= 0) && (x <= 10)) && (x != 5)}')

    def test_ranged_int_even(self):
        self.support_synthesis_with_ineq('{x:Integer where (x % 2) == 0}')

    def test_ranged_int_odd(self):
        self.support_synthesis_with_ineq('{x:Integer where !((x % 2) == 0)}')

    def test_ranged_int_with_implies(self):
        self.support_synthesis_with_ineq(
            '{x:Integer where ((x % 2) == 0) --> (x > 0)}')

    def test_ranged_int_with_lambda(self):
        self.support_synthesis_with_ineq(
            '{x:Integer where (\y:Integer -> x > y)(10)}')

    "Double"

    def test_ranged_double_not_range(self):
        self.support_synthesis_with_ineq(
            '{x:Double where !((x < 0.0) || (x > 10.0))}')

    def test_ranged_double_implies_and(self):
        self.support_synthesis_with_ineq(
            '{x:Double where (x > 10.0) --> ((x >= 10.0) && (x <= 20.0))}')

    "Boolean"

    def test_ranged_bool_true(self):
        self.support_synthesis_with_ineq('{x:Boolean where x == true}')

    def test_ranged_bool_true_or(self):
        self.support_synthesis_with_ineq('{x:Boolean where x || true}')

    def test_ranged_bool_not_x(self):
        self.support_synthesis_with_ineq('{x:Boolean where (x || true) --> x}')

    "String"

    def test_ranged_string_empty(self):
        self.support_synthesis_with_ineq(
            '{x:String where (String_size(x)) == 0}')

    def test_ranged_string_non_empty_up_to_10(self):
        self.support_synthesis_with_ineq(
            '{x:String where (String_size(x)) > 0 && (String_size(x)) < 10}')

    def test_ranged_string_even_length(self):
        self.support_synthesis_with_ineq(
            '{x:String where (String_size(x)) % 2 == 0}')

    # TODO: Consider attributes:

    #ty2('Person'),
    #ty2('{p:Person where (_Person_age(p)) >= 18 --> (_Person_height(p)) > 120}'),
    #ty2('{p:Person where (_Person_size(_Person_name(p))) == 3 }'),
