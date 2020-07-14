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


    def mk_bi_top(self, op, l, r):
        l = ex(l)
        r = ex(r)
        return Application(Application(TApplication(Var(op), t_delegate), l), r)

    def mk_bi_op(self, op, l, r):        
        return Application(Application(Var(op), l), r)
    

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


    # Test the Type Declaration
    def test_type_declaration(self):
        self.assert_prog("type Integer;", TypeDeclaration("Integer", star, None))
    

    # Test the Types
    def test_parens_type(self):
        self.assert_ty('(T)', BasicType('T'))
        self.assert_ty('(Integer)', BasicType('Integer'))
        
    def test_basic_type(self):        
        self.assert_ty('T', BasicType('T'))
        self.assert_ty('T1', BasicType('T1'))
        self.assert_ty('Integer', BasicType('Integer'))
        self.assert_ty('Test123_451', BasicType('Test123_451'))

    def test_refined_type(self):
        self.assert_ty('{x:Integer | true}', RefinedType('x', ty('Integer'), ex('true')))
        self.assert_ty('{x:{y:Integer | false} | true}', RefinedType('x',
                                            RefinedType('y', BasicType('Integer'),
                                            ex('false')), ex('true')))
    
    def test_abstraction_type(self):
        self.assert_ty('(x:Integer -> Double)', AbstractionType('x', ty('Integer'), ty('Double')))
        self.assert_ty('(x:(y:Integer -> Boolean) -> Double)', AbstractionType('x',
                                            AbstractionType('y', ty('Integer'),
                                            ty('Boolean')) , ty('Double')))
        self.assert_ty('(x:{y:Boolean | true} -> Double)', AbstractionType('x',
                                            RefinedType('y', ty('Boolean'),
                                            ex('true')) , ty('Double')))
    def test_typeapplication(self):
        self.assert_ty('List[Bool]', TypeApplication(ty('List'), ty('Bool')))
        self.assert_ty('List[List[Bool]]', TypeApplication(ty('List'),
                                    TypeApplication(ty('List'), ty('Bool'))))
        self.assert_ty('List[Int, Bool]', TypeApplication(TypeApplication(
                                    ty('List'), ty('Int')), ty('Bool')))

    
    def test_typeabstraction(self):
        pass
    

    # Test the statements
    def test_definition(self):
        pass
    
    def test_if_stmnt(self):
        pass

    def test_let(self):
        pass

    def test_assign(self):
        pass
    
    # Test the expressions
    def test_parens(self):
        self.assert_ex('(x)', ex('x'))
        self.assert_ex('(1)', ex('1'))
        self.assert_ex('(1.0)', ex('1.0'))

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
        self.assert_ex('1 + 1', self.mk_bi_top('+', "1", "1"))
        self.assert_ex('1 - 1', self.mk_bi_top('-', "1", "1"))
        self.assert_ex('1 - 2 * 3', self.mk_bi_top('-', "1", "2 * 3"))
        from aeon.interpreter import run
        print(">>", run(ex("2 * 3 - 7")))
        self.assert_ex('1 * 2 - 3', self.mk_bi_top('-', "1 * 2", "3"))
        
        
    def test_tapplication(self):
        pass
    
    def test_invocation(self):
        pass
    
    def test_not(self):
        pass
    
    def test_minus(self):
        pass

    def test_compare(self):
        pass
    
    def test_boolean(self):
        pass

    def test_abstraction(self):
        pass
    
    def test_if(self):
        pass

    def test_attribute(self):
        pass
    
    def test_improvement(self):
        pass

