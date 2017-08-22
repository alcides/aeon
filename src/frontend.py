import re

from parsec import *

from .ast import Node
from .typestructure import *

# ignore cases.
whitespace = regex(r'\s+', re.MULTILINE)
comment = regex(r'#.*')
ignore = many((whitespace | comment))

# lexer for words.

lexeme = lambda p: p << ignore  # skip all ignored characters.

t = lambda k: lexeme(string(k))

lpars = t('(')
rpars = t(')')
lbrace = t('{')
rbrace = t('}')
lbrack = t('[')
rbrack = t(']')
langle = t('<')
rangle = t('>')
colon = t(':')
comma = t(',')
arrow = t('->')
true = t('true').result(Node('literal', True, type=t_b))
false = t('false').result(Node('literal', False, type=t_b))
null = t('null').result(Node('literal', None, type=t_n))
symbol = lexeme(regex(r'[.\d\w_]+'))


op_1 = t("*") ^ t("/") ^ t("%")
op_2 = t("+") ^ t("-")
op_3 = t("<=") ^ t("<") ^ t(">=") ^ t(">") ^ t("==") ^ t("!=")


def number():
    '''Parse number.'''
    def fa(x):
        if "." not in x:
            return Node('literal', int(x), type=t_i)
        else:
            return Node('literal', float(x), type=t_f)
    
    return lexeme(
        regex(r'(0|[1-9][0-9]*)([.][0-9]+)?([eE][+-]?[0-9]+)?')
    ).parsecmap(fa)
    
def charseq():
    '''Parse string. (normal string and escaped string)'''
    def string_part():
        '''Parse normal string.'''
        return regex(r'[^"\\]+')

    def string_esc():
        '''Parse escaped string.'''
        return string('\\') >> (
            string('\\')
            | string('/')
            | string('b').result('\b')
            | string('f').result('\f')
            | string('n').result('\n')
            | string('r').result('\r')
            | string('t').result('\t')
            | regex(r'u[0-9a-fA-F]{4}').parsecmap(lambda s: chr(int(s[1:], 16)))
        )
    return string_part() | string_esc()

@lexeme
@generate
def invocation():
    s = yield symbol
    yield lpars
    args = yield sepBy(expr, comma)
    yield rpars
    return Node('invocation', s, args)
    


@lexeme
@generate
def expr_wrapped():
    o = yield expr
    return o
    
# helper
rotate = lambda x: Node(x[0][1], x[0][0], x[1])
makeblock = lambda xs: Node('block', *xs) 

symbol_e = symbol.parsecmap(lambda x: Node('atom', x))
block = (lbrace >> many(expr_wrapped)  << rbrace).parsecmap(makeblock)

@lexeme
@generate
def lambd():
    args = yield sepBy(symbol, comma)
    yield arrow
    e = yield block ^ expr
    return Node('lambda', args, e)
    
atom = number() ^ invocation ^ symbol_e ^ (lpars >> expr_wrapped << rpars) ^ lambd
expr_0 = (op_2 + atom).parsecmap(lambda x:Node(*x)) ^ atom
expr_1 = (expr_0 + op_1 + expr_0).parsecmap(rotate) ^ expr_0
expr_2 = (expr_1 + op_2 + expr_1).parsecmap(rotate) ^ expr_1
expr = (expr_2 + op_3 + expr_2).parsecmap(rotate) ^ expr_2

typee = (symbol + times(langle >> sepBy(symbol, comma) << rangle, 0, 1)).parsecmap(lambda x: Type(x[0], [ k[0] for k in x[1] ]))

@lexeme
@generate
def quoted():
    '''Parse quoted string.'''
    yield string('"')
    body = yield many(charseq())
    yield string('"')
    return ''.join(body)
    
@generate
def decl_args():
    arg = yield symbol
    yield colon
    typ = yield typee
    return Node('argument', arg, typ)
    
@lexeme
@generate
def decl():
    '''Parse function declaration.'''
    name = yield symbol
    yield colon
    yield lpars
    args = yield many(decl_args)
    yield rpars
    yield arrow
    ret = yield decl_args
    ret.nodet = 'rtype'
    yield lbrace
    body = yield many(expr).parsecmap(makeblock)
    yield rbrace
    return Node('decl', name, args, ret, body)

program = ignore >> many(decl)



if __name__ == '__main__':
    if len(sys.argv) > 1:
        i = open(sys.argv[1]).read()
    else:
        i = input()
    p = program.parse(i)
    print(p)