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

    def assert_prog(self, prog, expecteds):
        p = mk_parser().parse
        declarations = p(prog).declarations
        self.assertEqual(len(declarations), len(expecteds),
                         "Missing declaration / expected...")
        for decl, expected in zip(declarations, expecteds):
            self.assertEqual(decl, expected)


    def mk_bi_top(self, op, l, r):
        l = ex(l)
        r = ex(r)
        return Application(Application(TApplication(Var(op), t_delegate), l), r)

    def mk_bi_op(self, op, l, r):  
        l = ex(l)
        r = ex(r)      
        return Application(Application(Var(op), l), r)
    

    # Test the imports
    def test_import(self):
        self.assert_prog("import library;", [Import('library')])
        self.assert_prog("import path/to/library;", [Import('path/to/library')])
        
        self.assert_prog("import fun from library;", [Import('library', 'fun')])
        self.assert_prog("import fun from to/lib;", [Import('to/lib', 'fun')])
        
        self.assert_prog("import fun from to/../lib;", [Import('to/../lib', 'fun')])
        
    
    # Test the Type Alias
    def test_type_alias(self):
        self.assert_prog("type Test as Bool;", [TypeAlias('Test', ty('Bool'))])
        self.assert_prog("type Test as {x:Integer | x > 0};", 
                         [TypeAlias('Test', ty('{x:Integer | x > 0}'))])


    # Test the Type Declaration
    def test_type_declaration(self):
        self.assert_prog("type Integer;", [TypeDeclaration("Integer", star, None)])
        self.assert_prog("type List[T];", [TypeDeclaration("List", Kind(star, star), None)])
        self.assert_prog("type List[Int];", [TypeDeclaration("List", Kind(star, star), None)])
        self.assert_prog("type List[T, Int];", [TypeDeclaration("List", Kind(star, Kind(star, star)), None)])
    
    def test_type_declaration_params(self):
        self.assert_prog("type List {size:Integer;}", [TypeDeclaration("List", star, None),
                        Definition('List_size', ty('(_:List -> Integer)'), Var('uninterpreted'), ty('Integer'))])
    

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
        self.assert_ty('List[T]', TypeAbstraction('T', star, TypeApplication(ty('List'), ty('T'))))
        self.assert_ty('Map[X, Y]', TypeAbstraction('X', star,
                                    TypeAbstraction('Y', star,
                                    TypeApplication(TypeApplication(
                                    ty('Map'), ty('X')), ty('Y')))))
    
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
        self.assert_ex('2 - 3 * 7', self.mk_bi_top('-', "2", "3 * 7"))
        self.assert_ex('2 * 3 - 7', self.mk_bi_top('-', "2 * 3", "7"))
    
        
    def test_tapplication(self):
        self.assert_ex('f[T]', TAbstraction('T', star, Var('f')))
        self.assert_ex('f[Integer]', TApplication(Var('f'), ty('Integer')))
        self.assert_ex('f[T1, T2]', TApplication(TApplication(Var('f'),
                                                              ty('T1')),
                                                              ty('T2')))
        
    def test_invocation(self):
        self.assert_ex('f(1)', Application(Var('f'), ex('1')))
        self.assert_ex('f(x)(y)', Application(Application(Var('f'), ex('x')), ex('y')))
        self.assert_ex('f(x, y)', Application(Application(Var('f'), ex('x')), ex('y')))
        self.assert_ex('f[Integer](1)', Application(TApplication(Var('f'), ty('Integer')), ex('1')))
    
    def test_not(self):
        self.assert_ex('!true', Application(Var("!"), ex('true')))
        self.assert_ex('!x', Application(Var("!"), Var('x')))
        self.assert_ex('!1 > 3', Application(Var("!"), self.mk_bi_top('>', '1', '3')))
        self.assert_ex('! x > y', Application(Var("!"), self.mk_bi_top('>', 'x', 'y')))
        self.assert_ex('!false && true', Application(Application(Var("&&"),
                                                     Application(Var('!'), ex('false'))), 
                                                     ex('true')))
        self.assert_ex('true || !1>3', Application(Application(Var("||"),
                                                     ex('true')), 
                                                     Application(Var('!'), self.mk_bi_top('>', '1', '3'))))
        self.assert_ex('!1 > 3 --> true', Application(Application(Var("-->"),
                                                     Application(Var('!'), self.mk_bi_top('>', '1', '3'))), 
                                                     ex('true')))
    
    def test_minus(self):
        self.assert_ex('-x', Application(TApplication(Var('(-u)'), t_delegate), Var('x')))
        self.assert_ex('-1', Application(TApplication(Var('(-u)'), t_delegate), ex('1')))
        self.assert_ex('-x + y', self.mk_bi_top('+', '-x', 'y'))
            
    def test_compare(self):
        pass
    
    def test_boolean(self):
        self.assert_ex('true && false', Application(Application(Var('&&'),
                            ex('true')), ex('false')))
        self.assert_ex('true || 1 > 3', Application(Application(Var('||'),
                            ex('true')), self.mk_bi_top('>', '1', '3')))
        self.assert_ex('1 > 3 --> true', Application(Application(Var('-->'),
                            self.mk_bi_top('>', '1', '3')), ex('true')))
        self.assert_ex('x || y --> true', Application(Application(Var('-->'),
                            self.mk_bi_op('||', 'x', 'y')), ex('true')))
        self.assert_ex('true --> x || y', Application(Application(Var('-->'),
                            ex('true')), self.mk_bi_op('||', 'x', 'y')))
        self.assert_ex('(true && false) --> 1 > 3', Application(Application(Var('-->'),
                            self.mk_bi_op('&&', 'true', 'false')),
                            self.mk_bi_top('>', '1', '3')))
        self.assert_ex('x || y && z', Application(Application(Var('||'),
                            Var('x')), self.mk_bi_op('&&', 'y', 'z')))
        self.assert_ex('x && y || z', Application(Application(Var('||'),
                            self.mk_bi_op('&&', 'x', 'y')), Var('z')))
        self.assert_ex('!a && b || c', Application(Application(Var('||'),
                            Application(Application(Var('&&'), 
                                Application(Var("!"), Var('a'))), Var('b'))),
                            Var('c')))
    
    def test_abstraction(self):
        self.assert_ex('\\x:Integer -> x', Abstraction('x', ty('Integer'), ex('x')))
        self.assert_ex('(\\x:T -> x)[T][Integer]', TApplication(
                    TAbstraction('T', star, Abstraction('x', ty('T'), ex('x'))), ty('Integer')))
    
    def test_if(self):
        self.assert_ex('if x then y else z', If(Var('x'), Var('y'), Var('z')))
        self.assert_ex('if x then y else z + 1', If(Var('x'), Var('y'), 
                            self.mk_bi_top('+', 'z', '1')))
        self.assert_ex('if x then y else z || 1', If(Var('x'), Var('y'), 
                            self.mk_bi_op('||', 'z', '1')))
        self.assert_ex('1 && if x then y else z', Application((Application(Var('&&'), 
                            ex('1'))), If(Var('x'), Var('y'), Var('z'))))
        self.assert_ex('p && if x then y else z || d', Application((Application(Var('&&'), 
                            Var('p'))), If(Var('x'), Var('y'), self.mk_bi_op('||', 'z', 'd'))))

    def test_attribute(self):
        self.assert_ex('person.age', Var('person.age'))
        self.assert_ex('person.name.size', Var('person.name.size'))
    
    def test_improvement(self):
        self.assert_ex('@maximize()', Application(Var('@maximize'), Var('native')))
        self.assert_ex('@maximize(x)', Application(Var('@maximize'), Var('x')))
        self.assert_ex('@providecsv(x, y)', Application(Application(Var('@providecsv'), Var('x')), Var('y')))
