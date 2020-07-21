import os
from collections import deque
from lark import Lark, Transformer, v_args

from aeon.ast import *
from aeon.types import *
from aeon.frontend.utils import *

class TreeToAeon(Transformer):
    def __init__(self, path, context):
        super().__init__()

        self.context = context.copy()
        self.type_aliases = dict()
        self.declarations = list()

        self.path = path

    # -------------------------------------------------------------------------
    # Aeon Program
    def program(self, args):
        self.declarations += list(filter(None, args)) 
        self.declarations = resolve_imports(self.path, self.declarations)
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
        type_abstraction = remove_typeabs(typee)

        # Set the args to the ghost variables
        args = deque(args[1:])

        for ghost_name, ghost_type in args:
            ghost_name = f'{name}_{ghost_name}'
            function_type = AbstractionType('_', type_abstraction, remove_typeabs(ghost_type))
            function_type = process_typeabs(function_type)

            definition = Definition(ghost_name, function_type, 
                                    Var('uninterpreted').with_type(bottom),
                                    remove_typeabs(ghost_type))
            self.context[ghost_name] = function_type
            self.declarations.append(definition)

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
        (name, ttype), cond = args
        result = RefinedType(name, ttype, cond)
        return process_typeabs(result)
    
    def abstraction_type(self, args):
        (name, ttype), rtype = args
        result = AbstractionType(name, ttype, rtype)
        return process_typeabs(result)
    
    def type_tabstapp(self, args):
        ttype, (tabs, tapps) = args
        
        ttype = englobe_typeapps(ttype, tapps)
        ttype = remove_inner_typeabs(ttype, tabs)
        ttype = englobe_typeabs(ttype, tabs)
        
        return ttype

    def tabstractions(self, args):

        tabs = list()
        tapps = list()

        for typee in args:
            tabs += search_typeabs(typee)
            typee = remove_typeabs(typee)
            tapps.append(typee)

        return (list(dict.fromkeys(reversed(tabs))), tapps)

    def cname_ttype(self, args):
        self.context[args[0].value] = args[1]
        return (args[0].value, args[1])

    # -------------------------------------------------------------------------
    # Definition
    def native_definition(self, args):
        name, (tabs, tapps), params, rtype = preprocess_native(args)

        ttype = create_definition_ttype(params, rtype) if params \
                else AbstractionType('_', t_v, rtype)

        # TODO: o kind agora esta star, mas devia ser calculado
        ttype = englobe_typeabs(remove_typeabs(ttype), tabs)

        self.context[name] = ttype

        return Definition(name, ttype, Var('native'), rtype)

        
    def regular_definition(self, args):
        name, (tabs, tapps), params, rtype, body = preprocess_regular(args)
        
        if not params:
            params = [('_', t_v)]
        
        ttype = create_definition_ttype(params, rtype)
        
        # TODO: o kind eh star, mas devia ser calculado
        ttype = englobe_typeabs(remove_typeabs(ttype), tabs)

        # Apply the params to the body
        body = reduce(lambda abs_body, p: Abstraction(p[0], p[1], abs_body),
        reversed(params), body)

        # Apply the tabstractions to the body
        body = reduce(lambda abst, tee: TAbstraction(tee, star, abst),
        reversed(tabs), body)
        
        self.context[name] = ttype

        return Definition(name, ttype, body, rtype)

    def definition_params(self, args):
        return args
    

    # -------------------------------------------------------------------------
    # Statement
    def statement(self, args):
        return args[0]

    def if_statement(self, args):
        cond, then, otherwise = args
        return If(cond, then, otherwise)
    
    def let_statement(self, args):
        (name, typee), body = args
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
    def expr(self, args):
        return args[0]

    def expression(self, args):
        return args[0]

    def parens_expr(self, args):
        return args[0]
    
    def tapplication_expr(self, args):
        expr, (tabs, tapps) = args
        
        #tapps = list(filter(lambda tapp: True if not isinstance(tapp, BasicType) else
        #                                 tapp.name not in tabs, tapps))
    
        expr = reduce(lambda target, argument: TApplication(target, argument),
            tapps, expr)

        expr = reduce(lambda abst, ttype: TAbstraction(ttype, star, abst),
            tabs, expr)
        
        return expr 

    def invocation_expr(self, args):
        expression, parameters = args[0], args[1] if len(args) > 1 else [Var('native')]

        for param in parameters:
            expression = Application(expression, param)
        
        return expression
    
    def parameters(self, args):
        return args

    def not_expr(self, args):
        operator, expression = args
        return Application(Var(operator.value), expression)

    def minus_expr(self, args):
        operator, expression = args
        return Application(TApplication(Var("(-u)"), t_delegate), expression)
    
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
        (name, typee), body = args
        tabs = (list(dict.fromkeys(search_typeabs(typee) + search_tabs(body)))) 
        body = remove_tabs(body)
        return englobe_tabs(Abstraction(name, typee, body), reversed(tabs))
    
    def if_expr(self, args):
        cond, then, otherwise = args
        return If(cond, then, otherwise)
    
    def attribute_expr(self, args):
        names = list(map(lambda arg: arg.value, args))
        return generate_uninterpreted(self.context, names)
    
    def hole_expr(self, args):
        return Hole(args[0] if args else bottom)
        
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

    def improvement_expr(self, args):
        name = Var(f'@{args[0].value}')
        params = args[1] if len(args) > 1 else [Var('native')]
        return reduce(lambda target, p: Application(target, p), params, name)


# =============================================================================
# Creation of the parser
def mk_parser(rule="start", path="", context=dict()):
    return Lark.open(
        "aeon/frontend/aeon.lark",
        parser='lalr',
        #lexer='standard',
        start=rule,
        transformer=TreeToAeon(path, context))

p = mk_parser()
typee = mk_parser("ttype")
expr = mk_parser("expression")
stmnt = mk_parser("statement")
impt = mk_parser("aeimport")
