from ast import *
import sys

type_aliases = {}

precedence = (
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'EQUAL', 'NEQ', 'BEQ', 'BNEQ'),
    ('left', 'LT', 'GT', 'LTE', 'GTE'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'TIMES', 'DIV', 'MOD'),
    ('right', 'NOT', 'UMINUS'),
    ('right', 'POWER'),
)

# ---------------------------------- Program -----------------------------------
def p_init(t):
    """
    init : program
    """
    t[0] = Program(t[1])

def p_program(t):
    """
    program : (import | type_alias | type_declaration | function) program
    """
    t[0] = t[1] + t[2]

# ----------------------------------- Import -----------------------------------
def p_import(t):
    '''
    import : IMPORT import_name SEMICOLON
           | IMPORT import_name FROM IDENTIFIER SEMICOLON
    '''
    if len(t) == 3:
        t[0] = Import(t[2])
    else:
        t[0] = Import(t[2], t[4])

def p_import_name(t):
    """
    import_name : IDENTIFIER
                | DOT DOT import_name
                | IDENTIFIER DOT import_name
    """
    if len(t) == 2:
        t[0] = t[1]
    else:
        t[0] = '{}{}{}'.format(t[1], t[2], t[3])

# --------------------------- Type Alias & Decl --------------------------------
def p_type_alias(t):
    """
    type_alias : TYPE id AS id
    """
    name = t[2]
    alias = t[4]
    t[0] = TypeAlias(t[2], t[4])

def p_type_declaration(t):
    """
    type_declaration : 'null'
    """
    # TODO:
    pass

# -------------------------------- If then else --------------------------------
def p_if_then_else(t):
    """
    if_then_else : IF condition THEN expression ELSE expression
                 | IF condition LBRACE block RBRACE ELSE LBRACE block RBRACE
    """
    if len(t) == 7:
        t[0] = If(t[2], t[4], t[6])
    else:
        t[0] = If(t[2], t[4], t[8])


# --------------------------------- Functions ----------------------------------
def p_function(t):
    """
    function: id LPARENS ??? RPARENS RARROW id COLON ???
    """
    # TODO:
    pass

def p_block(t):
    """
    block : expression SEMICOLON
          | var_definition SEMICOLON
          | expression SEMICOLON block
    """
    if len(t) == 2:
        t[0] = Application(Abstraction(None, None, t[1]))   # to be filled after
    else:
        t[0] = Application(Abstraction(None, None, t[1]), t[2]) # to be filled after

# expression
def p_expression(t):
    """
    expression : LPAREN expression RPAREN
               | function_call
               | operation_call
               | if_then_else
               | abstraction
               | assignment
               | hole | id | literal
    """
    t[0] = (len(t) == 3) and t[2] or t[1]

# Abstraction
def p_abstraction(t):
    """
    abstraction: ABSTRACTION id COLON typee ARROW expression
    """
    t[0] = Abstraction(t[2], t[4], t[6])


# Assignment
def p_assignment(t):
    """
    assignment : id ASSIGNMENT expression
    """
    # TODO:
    pass

# Variable Definition
def p_var_definition(t):
    """
    var_definition : id COLON typee ASSIGNMENT expression
    """
    t[0] = Definition(t[1], t[3], t[5])
    pass

# Functional call
def p_function_call(t):
    """
    function_application : id LPAREN expression RPAREN
    """
    t[0] = Aplication(t[1], t[3])
    pass

# Operation call
def p_operation_call(t):
    """
    operation_call : expression operator expression
    """
    t[0] = Application(Aplication(t[2], t[1]), t[3])

# ----------------------------------- Types ------------------------------------
def p_typee(t):
    """
    typee : LPARENS typee RPARENS
          | type_abstraction
          | arrow_type
          | refined_type
          | type_application
          | basic_type
    """
    if len(typee) == 4:
        t[0] = t[2]
    else:
        t[0] = t[1]

def p_basic_type(t):
    """
    basic_type : TINTEGER
               | TFLOAT
               | TBOOLEAN
               | TSTRING
               | id
    """
    t[0] = t[1] in type_aliases and type_aliases[t[1]] or BasicType(t[1])

def p_refined_type(t):
    # Discordo da utilizacao de typee aqui
    """
    refined_type : LBRACE id COLON typee WHERE condition RBRACE
    """
    t[0] =

# TODO:
def p_arrow_type(t):
    pass

# TODO: Review kind
def p_type_abstraction(t):
    """
    type_abstraction : LPARENS id COMMA kind RPARENS FATARROW typee
    """
    t[0] = TypeAbstraction(t[2], t[4], t[7])

# TODO: O que eh isto ????????????????????????????
def p_type_application(t):
    """
    type_application :  LPARENS typee typee RPARENS
    """
    t[0] = TypeApplication(t[2], t[3])

# ---------------------------------- Kind --------------------------------------
# TODO: Review kind
def p_kind(t):
    """
    kind : KIND
    """
    t[0] = Kind()

def p_kind_recursive(t):
    """
    kind : LPARENS kind FATARROW kind RPARENS
    """
    t[0] = Kind(t[2], t[4])

# --------------------- Variables, literals and Operators ----------------------
def p_id(t):
    """
    id : IDENTIFIER
    """
    t[0] = Var(t[1])
    pass

def p_hole(t):
    """
    hole : HOLE
    """
    t[0] = Hole(t[1])

# Literals
def p_literal_boolean(t):
    """
    literal : BOOLEAN
    """
    value = t[1] == 'true' and True or False
    t[0] = Literal(value, type=refined_value(value, t_b, '_v'))

def p_literal_integer(t):
    """
    literal : INTEGER
    """
    t[0] = Literal(t[1], type=refined_value(int(x), t_i, '_v'))

def p_literal_float(t):
    """
    literal : FLOAT
    """
    t[0] = Literal(t[1], type=copy.deepcopy(t_f))

def p_literal_string(t):
    """
    literal : STRING
    """
    t[0] = Literal(t[1])

def p_uminus(t):
    """
    operator : MINUS expression %prec UMINUS
    """
    t[0] = Application(Var(t[1]), t[2])

def p_operator(t):
    """
    operator: PLUS | MIN | TIMES | DIV | MOD | POWER
            | AND | OR | NOT
            | EQ | NEQ | BEQ | BNEQ | LT | GT | LTE | GTE
    """
    t[0] = Var(t[1])

# ----------------------------------- Helper -----------------------------------
def refined_value(v, t, label="_v"):
    app1 = Application(Var(t == t_b and "===" or "=="), Var(label))
    app2 = Application(app1, Literal(v, type=t))
    return RefinedType(label, t, app2)
