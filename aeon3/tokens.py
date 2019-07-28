tokens = (
    # Import
    'IMPORT',
    'FROM',

    # Braces
    'LPAREN',
    'RPAREN',
    'LBRACE',
    'RBRACE',
    'LBRACKET',
    'RBRACKET',
    'LGUILLEMETS',
    'RGUILLEMETS',

    # Colons
    'COLON',
    'SEMICOLON',
    'COMMA',

    # Arrows
    'ARROW',
    'FATARROW',

    # Assignment
    'IDENTIFIER',
    'ASSIGNMENT',

    # Hole
    'HOLE',

    # If then else
    'IF',
    'THEN',
    'ELSE',

    # Comment
    'LCOMMENT',
    'BCOMMENT',

    # Math operators
    'PLUS',
    'MINUS',
    'TIMES',
    'DIV',
    'MOD',
    'POWER',

    # Logic operators
    'AND_STAT',
    'AND',
    'OR',
    'NOT',

    # Comparison operators
    'EQ',
    'NEQ',
    'BEQ',
    'BNEQ',
    'LT',
    'GT',
    'LTE',
    'GTE',

    # Others
    'UNDERSCORE',
    'ABSTRACTION',

    # Type
    'INTEGER',
    'FLOAT',
    'BOOLEAN',
    'STRING',
)

# Statements for tokens
t_LPAREN        = r'\('
t_RPAREN        = r'\)'
t_LBRACE        = r'{'
t_RBRACE        = r'}'
t_LBRACKET      = r'\['
t_RBRACKET      = r']'
t_LGUILLEMETS   = r'<'
t_RGUILLEMETS   = r'>'

t_COLON         = r':'
t_SEMICOLON     = r';'
t_COMMA         = r','

t_ARROW         = r'->'
t_FATARROW      = r'=>'

t_ASSIGNMENT    = r'='
t_HOLE          = r'_?_'    # temp hole, not a pretty hole

t_PLUS          = r'\+'
t_MINUS         = r'-'
t_TIMES         = r'\*'
t_DIV           = r'/'
t_MOD           = r'%'
t_POWER         = r'^'

t_AND           = r'&&'
t_OR            = r'\|\|'
t_NOT           = r'!'

t_EQ            = r'=='
t_NEQ           = r'!='
t_BEQ           = r'==='
t_BNEQ          = r'!=='
t_LT            = r'<'
t_GT            = r'>'
t_LTE           = r'<='
t_GTE           = r'>='

t_UNDERSCORE    = r'_'
t_ABSTRACTION   = r'\\'

reserved_keywords = {
    'import': 'IMPORT',
    'from': 'FROM',

    'if': 'IF',
    'then': 'THEN',
    'else': 'ELSE',

    'and': 'AND_STAT',
}

def t_IDENTIFIER(t):
    r'[a-zA-Z][a-zA-Z0-9_]*'
    if t.value in reserved_keywords:
        t.type = reserved_keywords[t.value]
    return t

def t_LCOMMENT(t):
    r'--[^\n]*'

def t_BCOMMENT(t):
    r'\'{3}[^\']*\'{3}'

def t_INTEGER(t):
    r'd+'
    try:
        t.value = int(t.value)
    except ValueError:
        raise ValueError("Integer value is too large %d", t.value)
    return t

def t_FLOAT(t):
    r'\d*[.]\d+'
    try:
        t.value = float(t.value)
    except ValueError:
        raise ValueError("Float value is too large %f", t.value)
    return t

def t_BOOLEAN(t): # pode dar problemas, confirmar
    r'[true|false]'
    t.value = t.value == 'true'
    return t

def t_STRING(t):
    r'\'[^\'\\]\'' # No escape strings so far
    return t

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

t_ignore = ' \t'

# Error handler
def t_error(t):
    print('Illegal character %s' % t.value[0])


import ply.lex as lex
lexer = lex.lex()
