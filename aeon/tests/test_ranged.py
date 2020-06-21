import unittest

from aeon.synthesis.inequalities import *
from aeon.libraries.stdlib import ty2

from aeon.ast import refined_value
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

    def assert_ranged(self, typee, times=10):
        T = ty2(typee)
        for _ in range(times):
            e = try_ranged(self.ctx, T)
            self.assertIsNotNone(e.value)
            check_type(self.ctx, e, T)

    "Integer"
    
    def test_lower_bounded_int(self):
        self.assert_ranged('{x:Integer where (x >= 0)}')

    def test_upper_bounded_int(self):
        self.assert_ranged('{x:Integer where (x <= 0)}')
    
    def test_ranged_int_closed_range(self):
        self.assert_ranged('{x:Integer where (x >= 0) && (x <= 10)}')
    
    def test_ranged_int_restricted_range(self):
        self.assert_ranged('{x:Integer where (x >= 0) && (x <= 0)}')
    
    def test_ranged_int_closed_range_with_hole(self):
        self.assert_ranged(
            '{x:Integer where ((x >= 0) && (x <= 10)) && (x != 5)}')

    def test_ranged_int_or(self):
        self.assert_ranged('{x:Integer where (x <= 0) || (x >= 0)}')

    def test_ranged_int_or_2(self):
        self.assert_ranged('{x:Integer where (x <= (0-10)) || (x >= 10)}')
    
    def test_ranged_int_or_3(self):
        self.assert_ranged('{x:Integer where ((x < 0) && (x > (0-10))) || '
                                            '((x > 0) && (x < 10))}')
    
    def test_ranged_int_or_4(self):
        # Generates the intervals [0, 10], [5, 10], [0, 20], [5, 20]
        self.assert_ranged('{x:Integer where ((x >= 0) || (x >= 5)) && '
                                            '((x <= 10) || (x <= 20))}')
    
    def test_ranged_int_ultimate_or(self):
        # Generates the intervals [0, 10], [5, 10], [0, 20], [5, 12]
        self.assert_ranged('{x:Integer where ((x >= 0) || ((x <= 12) && '
                              '(x >= 5))) && ((x <= 10) || (x <= 20))}')
    '''
    def test_ranged_int_even(self):
        self.assert_ranged('{x:Integer where (x % 2) == 0}')

    def test_ranged_int_odd(self):
        self.assert_ranged('{x:Integer where !((x % 2) == 0)}')
    
    def test_ranged_int_even_positive(self):
        self.assert_ranged('{x:Integer where ((x % 2) == 0) --> (x > 0)}')
    '''
    def test_ranged_int_with_lambda(self):
        self.assert_ranged('{x:Integer where ((\\y:Integer -> x > y) 10)}')
    
    def test_ranged_int_implies(self):
        self.assert_ranged('{x:Integer where (x > 0) --> (x == 5)}')
    
    def test_ranged_int_implies_2(self):
        self.assert_ranged('{x:Integer where (x > 0) && (((x > 10) && '
                                            '(x < 20)) --> (x == 15))}')
    
    def test_ranged_int_left_sum(self):
        self.assert_ranged('{x:Integer where (x + 1) > 0}')
    
    def test_ranged_int_right_sum(self):
        self.assert_ranged('{x:Integer where x > (3 + 3 - 6)}')
    
    def test_ranged_int_left_mult(self):
        self.assert_ranged('{x:Integer where (x * 2) > 2}')
    
    def test_ranged_int_right_mult(self):
        self.assert_ranged('{x:Integer where x > ((3 * 3) - 6)}')
    
    def test_ranged_int_sum_x(self):
        self.assert_ranged('{x:Integer where ((x + x) + x) > 9}')
    
    def test_ranged_int_power_x(self):
        self.assert_ranged('{x:Integer where (x * x) > 11}')
    
    def test_ranged_int_left_div(self):
        self.assert_ranged('{x:Integer where (x / 2) > 5}')
    
    def test_ranged_int_right_div(self):
        self.assert_ranged('{x:Integer where x > (10 / 2)}')
    
    def test_ranged_int_div_by_x(self):
        self.assert_ranged('{x:{x:Integer where (x != 0)} where (10 / x) > 2}')
    
    def test_ranged_int_not(self):
        self.assert_ranged('{x:Integer where !(x > 0)}')
    
    def test_ranged_int_not_2(self):
        self.assert_ranged('{x:Integer where !((x < 0) || (x > 10))}')
    
    def test_ranged_int_not_4(self):
        self.assert_ranged('{x:Integer where !((x < 0) && (x > 10))}')

    def test_ranged_int_not_5(self):
        self.assert_ranged('{x:Integer where (!(x > 0)) --> (x == (0-5))}')

    def test_ranged_int_not_with_hole(self):
        self.assert_ranged('{x:Integer where (x > 0) --> ((x > 0) && (x < 10) && (!(x == 5)))}')
    
    "Double"

    def test_ranged_double_not_range(self):
        self.assert_ranged('{x:Double where !((x < 0.0) || (x > 10.0))}')

    def test_ranged_double_implies_and(self):
        self.assert_ranged('{x:Double where (x > 10.0) --> ((x >= 10.0) && (x <= 20.0))}')

    def test_ranged_double_div_by_x(self):
        self.assert_ranged('{x:{x:Double where (x != 0)} where (10 / x) > 2}')

    "Boolean"

    def test_ranged_bool_true(self):
        self.assert_ranged('{x:Boolean where x == true}')

    def test_ranged_bool_true_or(self):
        self.assert_ranged('{x:Boolean where x || true}')

    def test_ranged_bool_not_x(self):
        self.assert_ranged('{x:Boolean where (x || true) --> x}')

    '''
    "String"

    def test_ranged_string_empty(self):
        self.assert_ranged('{x:String where (String_size(x)) == 0}')

    def test_ranged_string_non_empty_up_to_10(self):
        self.assert_ranged('{x:String where (String_size(x)) > 0 && (String_size(x)) < 10}')

    def test_ranged_string_even_length(self):
        self.assert_ranged('{x:String where (String_size(x)) % 2 == 0}')

    # TODO: Consider attributes:

    #ty2('Person'),
    #ty2('{p:Person where (_Person_age(p)) >= 18 --> (_Person_height(p)) > 120}'),
    #ty2('{p:Person where (_Person_size(_Person_name(p))) == 3 }'),
    '''