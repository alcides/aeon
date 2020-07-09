import os
from collections import deque
from lark import Lark, Transformer, v_args

from aeon.ast import *
from aeon.types import *
from aeon.frontend.utils import *

class TreeToAeon(Transformer):
    def __init__(self):
        super().__init__()

        self.context = dict()
        self.type_aliases = dict()
        self.declarations = list()

    # -------------------------------------------------------------------------
    # Aeon Program
    def program(self, args):
        self.declarations += list(filter(None, args)) 
        return Program(self.declarations)

    def aeon(self, args):
        return args[0]

    # -------------------------------------------------------------------------
    # Import statements        
    def function_import(self, args):
        return Import(args[1].value, args[0].value)

    def regular_import(self, args):
        return Import(args[0])

    # -------------------------------------------------------------------------
    # Type Alias
    def type_alias(self, args):
        name, typee = args[0].value, args[1]
        self.type_aliases[name] = typee
        return TypeAlias(name, typee)

    # -------------------------------------------------------------------------
    # Type Declaration
    def regular_type_decl(self, args):
        typee = args[0]
        name = get_type_name(typee)
        kind = get_type_kind(typee)
        return TypeDeclaration(name, kind, None)

    def param_type_decl(self, args):
        typee = args[0]
        name = get_type_name(typee)
        kind = get_type_kind(typee)

        self.declarations.append(TypeDeclaration(name, kind, None))

        # Now it is time to deal with the uninterpreted functions
        type_abstraction, _ = extract_refinements(typee)

        # Set the args to the ghost variables
        args = deque(args[1:])

        while args:
            ghost_name = f'{name}_{args.popleft().value}'
            ghost_type = args.popleft()
            function_type = AbstractionType('_', type_abstraction, remove_tabs(ghost_type))
            function_type = wrap_typeabstractions(function_type, typee)

            definition = Definition(ghost_name, function_type, 
                                    Var('uninterpreted').with_type(bottom),
                                    remove_tabs(ghost_type))
            self.declarations.append(definition)
            self.context[ghost_name] = function_type

        return None
    
        
    # -------------------------------------------------------------------------
    # Types
    def parens_type(self, args):
        return args[0]
        
    def basic_type(self, args):
        value = args[0].value
        if value in self.type_aliases:
            return self.type_aliases[value]
        return BasicType(value)
        
    def refined_type(self, args):
        return RefinedType(args[0].value, args[1], args[2])
    
    def abstraction_type(self, args):
        return AbstractionType(args[0].value, args[1], args[2])

    def type_absapp(self, args):
        pass
        
    # -------------------------------------------------------------------------
    # Definition
    def native_definition(self, args):
        pass
        
    def regular_definition(self, args):
        pass
    
    def tabstractions(self, args):
        pass

    def definition_params(self, args):
        pass
    
    # -------------------------------------------------------------------------
    # Statement
    def statement(self, args):
        return args[0]

    def if_statement(self, args):
        cond, then, otherwise = args
        return If(cond, then, otherwise)
    
    def let_statement(self, args):
        name, typee, body = args[0].value, args[1], args[2]
        self.context[name] = typee
        return Definition(name, typee, body, typee)

    def assign_statement(self, args):
        name, body = args[0].value, args[1]
        typee = self.context[name]
        return Definition(name, typee, body, typee)

    def expression_statement(self, args):
        return args[0]

    # -------------------------------------------------------------------------
    # Expressions
    def expression(self, args):
        return args[0]

    def parens_expr(self, args):
        return args[0]
    
    def tapplication_expr(self, args):
        pass
    
    def invocation_expr(self, args):
        pass
    
    def parameters(self, args):
        return args

    def not_expr(self, args):
        operator, expression = args

        if isinstance(expression, Literal):
                expression.value = not expression.value
                expression.type.cond.argument.value = not expression.type.cond.argument.value
        else:
            expression = Application(Var(operator.value), expression)

        return expression

    def minus_expr(self, args):
        # TODO: must properley know the type of the right side
        operator, expression = args
        left = Literal(0, refined_value(0, t_i))
        tapp = TApplication(Var(operator.value), t_delegate)
        expression = Application(Application(tapp, left), expression)
    
    def arithmetic_expr(self, args):
        left, operator, right = args
        tapp = TApplication(Var(operator.value), t_delegate)
        return Application(Application(tapp, left), right)
    
    def compare_expr(self, args):
        left, operator, right = args
        tapp = TApplication(Var(operator.value), t_delegate)
        return Application(Application(tapp, left), right)

    def boolean_expr(self, args):
        left, operator, right = args
        return Application(Application(Var(operator.value), left), right)
    
    def abstraction_expr(self, args):
        name, typee, body = args
        return Abstraction(name.value, typee, body)
    
    def if_expr(self, args):
        cond, then, otherwise = args
        return If(cond, then, otherwise)
    
    def attribute_expr(self, args):
        pass
    
    def hole_expr(self, args):
        return Hole(args[0] if args else None)
        
    def variable_expr(self, args):
        return Var(args[0].value)
    
    def literal_expr(self, args):
        ttype, value = args[0].type, args[0].value
        
        if ttype == 'INTLIT':
            value, tee = int(value), t_i
        elif ttype == 'FLOATLIT':
            value, tee = float(value), t_f
        elif ttype == 'BOOLLIT':
            value, tee = value == 'true' and True or False, t_b
        elif ttype == 'STRINGLIT':
            value, tee = value[1:-1], t_s
        else:
            raise Exception("Error when parsing literal:", ttype)

        return Literal(value, refined_value(value, tee))



def mk_parser(rule="start"):
    return Lark.open(
        "aeon/frontend/aeon.lark",
        parser='lalr',
        #lexer='standard',
        start=rule,
        transformer=TreeToAeon())

p = mk_parser()
typee = mk_parser("ttype")
expr = mk_parser("expression")
stmnt = mk_parser("statement")
