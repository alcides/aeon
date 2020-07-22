import unittest

from aeon.ast import *
from aeon.types import *
from aeon.frontend.frontend import mk_parser

ty = mk_parser('ttype').parse
ex = mk_parser('expression').parse
imprt = mk_parser('aeimport').parse

class TestFrontend(unittest.TestCase):
    def assert_ty(self, typee, expected):
        tee = ty(typee)
        self.assertEqual(tee, expected)

    def assert_ex(self, expression, expected):
        expr = ex(expression)
        self.assertEqual(expr, expected)

    def assert_import(self, expression, expected):
        expr = imprt(expression)
        self.assertEqual(expr, expected)

    def assert_prog(self, prog, expecteds):
        p = mk_parser().parse
        declarations = p(prog).declarations
        self.assertEqual(len(declarations), len(expecteds),
                         "Missing declaration / expected...")
        for decl, expected in zip(declarations, expecteds):
            self.assertEqual(decl, expected)
    
    def mk_un_op(self, op, exp):
        op = ex(op)
        exp = ex(exp)
        return Application(op, exp)

    def mk_bi_top(self, op, l, r):
        l = ex(l)
        r = ex(r)
        return Application(Application(TApplication(Var(op), t_delegate), l), r)

    def mk_bi_op(self, op, l, r):  
        l = ex(l)
        r = ex(r)      
        return Application(Application(Var(op), l), r)
    
    
    # Test the imports: No longer makes sense as imports are automatically done
    def test_import(self):
        # self.assert_import("import library;", Import('library'))
        # self.assert_import("import path/to/library;", Import('path/to/library'))
        
        # self.assert_import("import fun from library;", Import('library', 'fun'))
        # self.assert_import("import fun from to/lib;", Import('to/lib', 'fun'))
        
        # self.assert_import("import fun from to/../lib;", Import('to/../lib', 'fun'))
        pass

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
                        Definition('List_size', ty('(_:List -> Integer)'), Var('uninterpreted'), t_i)])

        self.assert_prog("type List {x:Integer; y:Double;}", [TypeDeclaration("List", star, None),
                        Definition('List_x', ty('(_:List -> Integer)'), Var('uninterpreted'), t_i),
                        Definition('List_y', ty('(_:List -> Double)'), Var('uninterpreted'), t_f)])

        self.assert_prog("type List[T] {size:Integer;}", [TypeDeclaration("List", Kind(star, star), None),
                        Definition('List_size', ty('(_:List[T] -> Integer)'), Var('uninterpreted'), t_i)])
    

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
        self.assert_ty('{x:Integer | true}', RefinedType('x', t_i, ex('true')))
        self.assert_ty('{x:{y:Integer | false} | true}', RefinedType('x',
                                            RefinedType('y', BasicType('Integer'),
                                            ex('false')), ex('true')))
    
    def test_abstraction_type(self):
        self.assert_ty('(x:Integer -> Double)', AbstractionType('x', t_i, t_f))

        self.assert_ty('(_:List[T] -> Integer)', TypeAbstraction('T', star, 
                                AbstractionType('_', TypeApplication(ty('List'), ty('T')), t_i)))

        self.assert_ty('{_:List[T] | true}', TypeAbstraction('T', star, 
                                RefinedType('_', TypeApplication(ty('List'), ty('T')), ex('true'))))
        
        self.assert_ty('(x:X -> (y:Y -> Double))', TypeAbstraction('X', star,
                                                   TypeAbstraction('Y', star,
                                                   AbstractionType('x', ty('X'),
                                                   AbstractionType('y', ty('Y'), ty('Double'))))))

        self.assert_ty('(x:(y:Integer -> Boolean) -> Double)', AbstractionType('x',
                                            AbstractionType('y', t_i, t_b) , t_f))

        self.assert_ty('(x:{y:Boolean | true} -> Double)', AbstractionType('x',
                                            RefinedType('y', t_b, ex('true')) , t_f))

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
    def test_definition_native(self):
        self.assert_prog("f() -> Integer;", [Definition('f', ty('(_:Void -> Integer)'), ex('native'), ty('Integer'))])
        self.assert_prog("f(x:Bool) -> Double;", [Definition('f', ty('(x:Bool -> Double)'), ex('native'), ty('Double'))])
        self.assert_prog("f(x:Bool, y:Int) -> Double;", [Definition('f', ty('(x:Bool -> (y:Int -> Double))'), ex('native'), ty('Double'))])
        self.assert_prog("f[Integer](x:Bool, y:Int) -> Double;", [Definition('f', ty('(x:Bool -> (y:Int -> Double))'), ex('native'), ty('Double'))])
        self.assert_prog("f[T](x:Bool, y:Int) -> Double;", [Definition('f', TypeAbstraction('T', star, ty('(x:Bool -> (y:Int -> Double))')), ex('native'), ty('Double'))])
        self.assert_prog("f[X, Y](x:X, y:Y) -> Double;", [Definition('f', ty('(x:X -> (y:Y -> Double))'), ex('native'), ty('Double'))])
        self.assert_prog("f[X](x:X) -> X;", [Definition('f', ty('(x:X ->  X)'), ex('native'), ty('X'))])
        self.assert_prog("f[X, Integer](x:X, y:Integer) -> Double;", [Definition('f', ty('(x:X -> (y:Integer -> Double))'), ex('native'), ty('Double'))])

    def test_definition_regular(self):
        self.assert_prog('''f() -> Integer {
            x;
        }''', [Definition('f', ty('(_:Void -> Integer)'), Abstraction('_', ty('Void'), ex("x")), ty('Integer'))])
        
    def test_if_stmnt(self):
        pass

    def test_let(self):
        self.assert_prog('x : T = 1;', [Definition('x', ty('T'), ex('1'), ty('T'))])
        self.assert_prog('x : Integer = 1;', [Definition('x', ty('Integer'), ex('1'), ty('Integer'))])
        self.assert_prog('x : Double = 1; x = 2;', [Definition('x', ty('Double'), ex('1'), ty('Double')), 
                                                    Definition('x', t_f, ex('2'), t_f)])

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
        self.assert_ex('??', Hole(bottom))
        self.assert_ex('?Integer?', Hole(BasicType('Integer')))
    
    def test_arithmetic_expr(self):
        self.assert_ex('1 + 1', self.mk_bi_top('+', "1", "1"))
        self.assert_ex('1 - 1', self.mk_bi_top('-', "1", "1"))
        self.assert_ex('2 - 3 * 7', self.mk_bi_top('-', "2", "3 * 7"))
        self.assert_ex('2 * 3 - 7', self.mk_bi_top('-', "2 * 3", "7"))
    
        
    def test_tapplication(self):
        self.assert_ex('f[T]', TAbstraction('T', star, TApplication(Var('f'), ty('T'))))
        self.assert_ex('f[Integer]', TApplication(Var('f'), t_i))
        self.assert_ex('f[T1, T2]', TApplication(TApplication(Var('f'),
                                                              ty('T1')),
                                                              ty('T2')))
        self.assert_ex('f[Integer]()', Application(TApplication(ex('f'),
                                      ty('Integer')), ex('native')))
        self.assert_ex('f[List[Integer]](l)', Application(TApplication(ex('f'),
                         TypeApplication(ty('List'), ty('Integer'))), ex('l')))


    def test_invocation(self):
        self.assert_ex('f(1)', Application(Var('f'), ex('1')))
        self.assert_ex('f(x)(y)', Application(Application(Var('f'), ex('x')), ex('y')))
        self.assert_ex('f(x, y)', Application(Application(Var('f'), ex('x')), ex('y')))
        self.assert_ex('f[Integer](1)', Application(TApplication(Var('f'), t_i), ex('1')))
    
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
        self.assert_ex('x == y', self.mk_bi_top('==', 'x', 'y'))
        self.assert_ex('x != y', self.mk_bi_top('!=', 'x', 'y'))
        self.assert_ex('x - 1 > y', self.mk_bi_top('>', 'x-1', 'y'))
        self.assert_ex('x && z > y', self.mk_bi_op('&&', 'x', 'z > y'))
        self.assert_ex('x && z != y', self.mk_bi_op('&&', 'x', 'z != y'))
    
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
        self.assert_ex('\\x:Integer -> x', Abstraction('x', t_i, ex('x')))
        self.assert_ex('(\\x:T -> x)[Integer]', TApplication(
                    TAbstraction('T', star, Abstraction('x', ty('T'), ex('x'))), t_i))
        self.assert_ex('(\\x : T -> f[T])',
                        TAbstraction('T', star, Abstraction('x', ty('T'), TApplication(ex('f'), ty('T')))))
        self.assert_ex('(\\x : T -> \\y:Y -> f[T])',
                        TAbstraction('T', star, TAbstraction('Y', star, Abstraction('x', ty('T'), Abstraction('y', ty('Y'), TApplication(ex('f'), ty('T')))        )   )    ))
        self.assert_ex('(\\x : T -> f[T](x))[Integer](10)',
                        Application(TApplication(TAbstraction('T', star,
                            Abstraction('x', ty('T'), 
                            Application(TApplication(ex('f'), ty('T')), ex('x')))), ty('Integer')), ex('10')))
    
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
        #self.assert_ex('person.name.size', Var('person.name.size'))
        
        self.assert_prog('''type Person{age:Integer;}
                            person : Person = 1;
                            person.age;''', 
                            [TypeDeclaration("Person", star, None),
                             Definition("Person_age", ty('(_:Person -> Integer)'), ex('uninterpreted'), ty('Integer')),
                             Definition("person", ty("Person"), ex("1"), ty("Person")),
                             Application(Var('Person_age'), Var("person"))])
        self.assert_prog('''
                        type String {size:Integer;}
                        type Person {name:String;}
                        person : Person = 1;
                        person.name.size;''', 
                        [TypeDeclaration("String", star, None),
                         Definition("String_size", ty('(_:String -> Integer)'), ex('uninterpreted'), ty('Integer')),
                         TypeDeclaration("Person", star, None),
                         Definition("Person_name", ty('(_:Person -> String)'), ex('uninterpreted'), ty('String')),
                         Definition("person", ty("Person"), ex("1"), ty("Person")),
                         Application(Var('String_size'), Application(Var('Person_name'), Var("person")))])

        self.assert_prog('''
                type List[T] {size:Integer;}
                l : List[Integer] = 1;
                l.size;''', 
                [TypeDeclaration("List", Kind(star, star), None),
                 Definition("List_size", ty('(_:List[T] -> Integer)'), ex('uninterpreted'), ty('Integer')),
                 Definition("l", ty("List[Integer]"), ex("1"), ty("List[Integer]")),
                 Application(TApplication(Var('List_size'), ty('Integer')), Var('l'))])
        
        self.assert_prog(
                '''
                type List[T] {size:Integer;}
                empty[T]() -> {l:List[T] | l.size};
                l : List[Integer] = empty[Integer]();
                ''', 
                [TypeDeclaration("List", Kind(star, star), None),
                 Definition("List_size", ty('(_:List[T] -> Integer)'), ex('uninterpreted'), ty('Integer')),
                 Definition("empty", TypeAbstraction('T', star, AbstractionType('_', ty('Void'),
                    RefinedType('l', TypeApplication(ty('List'), ty('T')), Application(TApplication(Var('List_size'), ty('T')), Var('l'))))),
                    ex("native"),
                    RefinedType('l', TypeApplication(ty('List'), ty('T')), Application(TApplication(Var('List_size'), ty('T')), Var('l')))),
                 Definition("l", ty("List[Integer]"), ex('empty[Integer]()'), ty("List[Integer]"))])
    
    def test_improvement(self):
        self.assert_ex('@maximize()', Application(Var('@maximize'), Var('native')))
        self.assert_ex('@maximize(x)', Application(Var('@maximize'), Var('x')))
        self.assert_ex('@providecsv(x, y)', Application(Application(Var('@providecsv'), Var('x')), Var('y')))
    