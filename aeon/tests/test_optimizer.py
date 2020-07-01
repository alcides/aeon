import unittest

from aeon.optimizer import optimize
from aeon.frontend_core import expr, typee

ex = expr.parse
ty = typee.parse


class TestOptimizer(unittest.TestCase):
    def assert_expr(self, expression, expected):
        expression = optimize(ex(expression))
        expected = ex(expected)
        self.assertEqual(expression, expected)

    ''' TypedNode '''
    
    # Literals    
    def test_literal(self):
        self.assert_expr('1', '1')
        self.assert_expr('1.0', '1.0')
        self.assert_expr('true', 'true')
        self.assert_expr('\"text\"', '\"text\"')

    # Variables
    def test_variable(self):
        self.assert_expr('x', 'x')
    
    # If
    def test_basic_if(self):
        self.assert_expr('if true then 1 else 0', '1')
        self.assert_expr('if false then 1 else 0', '0')
        self.assert_expr('if x then 1 else 0', 'if x then 1 else 0')
        self.assert_expr('if (f 1) then 1 else 0', 'if (f 1) then 1 else 0')
        
    def test_if_cond_operations(self):
        self.assert_expr('if (true || false) then 1 else 0', '1')
        self.assert_expr('if (true && false) then 1 else 0', '0')
        self.assert_expr('if (true --> false) then 1 else 0', '0')

        self.assert_expr('if (1 > 0) then 1 else 0', '1')
        self.assert_expr('if (1 < 0) then 1 else 0', '0')
        self.assert_expr('if (1 >= 1) then 1 else 0', '1')
        self.assert_expr('if (1 <= 0) then 1 else 0', '0')

        self.assert_expr('if (x > 0) then 1 else 0', 'if (x > 0) then 1 else 0')
        self.assert_expr('if (x < 0) then 1 else 0', 'if (x < 0) then 1 else 0')

    def test_if_body_operations(self):        
        self.assert_expr('if (f x) then 1 else 1', '1')
        self.assert_expr('if x then (f x) else (f x)', '(f x)')
        self.assert_expr('if x then (1 + 1) else 2', '2')
    
    # Application
    def test_application_basic(self):
        self.assert_expr('1 + 1', '2')
        self.assert_expr('1 * 0', '0')
        self.assert_expr('1 - 1', '0')
        self.assert_expr('0 / 1', '0')
    
        # Composed operations
        self.assert_expr('(3 * 5) - (2 / 2)', '14')
    
    def test_application_variable(self):
        self.assert_expr('0 / x', '0')
    
        self.assert_expr('x + 1', 'x + 1')
        self.assert_expr('x * 1', 'x')
        self.assert_expr('x * (2 - 1)', 'x')
        self.assert_expr('0 * x', '0')
    
    def test_application_abstraction(self):
        self.assert_expr('((\\x:Integer -> x) 1)', '1')
        self.assert_expr('((\\x:Integer -> 2) 1)', '2')
        self.assert_expr('((\\x:Integer -> (x + 1)) 2)', '3')
        self.assert_expr('((\\x:Integer -> (f 2)) y)', '(f 2)')
    

    # Abstractions
    def test_abstraction_basic(self):
        self.assert_expr('\\x:Integer -> \\y:Integer -> 1', '1')
        self.assert_expr('\\x:Integer -> \\y:Integer -> x', '\\x:Integer -> x')
        self.assert_expr('\\x:Integer -> \\y:Integer -> x + y', '\\x:Integer -> \\y:Integer -> x + y')
    
    def test_abstraction_if(self):
        self.assert_expr('\\x:Integer -> (if true then 1 else x)', '1')
        self.assert_expr('\\x:Integer -> (if false then 1 else x)', '\\x:Integer -> x')

    # TApplications
    def test_tapplication_basic(self):
        self.assert_expr('f[Integer]', 'f[Integer]')

    # TAbstractions
    def test_tabstraction_basic(self):
        pass
