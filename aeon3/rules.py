from ast import *
import sys

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
        t[0] = '{}.{}'.format(t[1], t[3])


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


# ---------------------------- Block of expressions -----------------------------
def p_block(t):
    """
    block : expression
          | expression block
    """
    if len(t) == 2:
        t[0] = Application(Abstraction(None, None, t[1]))   # to be filled after
    else:
        t[0] = Application(Abstraction(None, None, t[1]), t[2]) # to be filled after

# expression
def p_expression(t):
    # TODO: Permite comportamento talvez indesejado: (asd : Integer = 1)
    """
    expression : (LPAREN expression RPAREN
              | var_definition
              | function_call
              | operation_call
              | if_then_else
              | abstraction
              | assignment
              | hole | id | literal) SEMICOLON
    """
    t[0] = (len(t) == 3) and t[2] or t[1]

# Abstraction
def p_abstraction(t):
    """
    abstraction: ABSTRACTION id COLON typee ARROW expression
    """
    t[0] = Abstraction(t[2], t[4], t[6])
    pass


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

# ------------------------------------ Type ------------------------------------
def p_typee(t):
    """
    typee :
    """
    # TODO:
    pass

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

def p_literal(t):
    """
    literal : INTEGER | FLOAT | STRING
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
