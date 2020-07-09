import unittest

from aeon.ast import *
from aeon.types import *
from aeon.frontend.frontend import mk_parser

ty = mk_parser('ttype').parse
ex = mk_parser('expression').parse

class TestFrontend(unittest.TestCase):
    def assert_ty(self, typee, expected):
        tee = ty(typee)
        self.assertEqual(tee, expected)

    def assert_ex(self, expression, expected):
        expr = ex(expression)
        self.assertEqual(expr, expected)

    def assert_prog(self, prog, expected):
        p = mk_parser().parse
        decl = p(prog).declarations[0]
        self.assertEqual(decl, expected)

    # Test the imports
    def test_import(self):
        self.assert_prog("import library;", Import('library'))
        self.assert_prog("import path/to/library;", Import('path/to/library'))
        
        self.assert_prog("import fun from library;", Import('library', 'fun'))
        self.assert_prog("import fun from to/lib;", Import('to/lib', 'fun'))
        
        self.assert_prog("import fun from to/../lib;", Import('to/../lib', 'fun'))
        
    # Test the Type Alias
    def test_type_alias(self):
        self.assert_prog("type Test as Bool;", TypeAlias('Test', BasicType('Bool')))


    # Test the TypeDeclaration
    def test_type_declaration(self):
        self.assert_prog("type Integer;", TypeDeclaration("Integer", star, None))
        
    # Test the types
    def test_basic_type(self):        
        self.assert_ty('T', BasicType('T'))
        self.assert_ty('T1', BasicType('T1'))
        self.assert_ty('Integer', BasicType('Integer'))
        self.assert_ty('Test123_451', BasicType('Test123_451'))

    def test_refined_type(self):
        self.assert_ty('{x:Integer | true}', RefinedType('x', BasicType('Integer'), Literal(True, t_b)))
    
    # Test the expressions
    def test_literal(self):
        self.assert_ex('1', Literal(1, refined_value(1, t_i)))
        self.assert_ex('2.0', Literal(2.0, refined_value(2.0, t_f)))
        self.assert_ex('true', Literal(True, refined_value(True, t_b)))
        self.assert_ex('false', Literal(False, refined_value(False, t_b)))
        self.assert_ex('\"String\"', Literal("String", refined_value("String", t_s)))
    
    def test_var(self):
        self.assert_ex('x', Var('x'))
        with self.assertRaises(Exception):
            self.assert_ex('X', Var('X'))
    
    def test_hole(self):
        self.assert_ex('??', Hole(None))
        self.assert_ex('?Integer?', Hole(BasicType('Integer')))
    
    def test_arithmetic_expr(self):
        #self.assert_ex('1+1', )
        pass
