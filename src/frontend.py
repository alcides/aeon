import re
import os

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
fatarrow = t('=>')
true = t('true').result(Node('literal', True, type=t_b))
false = t('false').result(Node('literal', False, type=t_b))
null = t('null').result(Node('literal', None, type=t_n))
symbol = lexeme(regex(r'[.\d\w_]+'))


op_1 = t("*") ^ t("/") ^ t("%")
op_2 = t("+") ^ t("-")
op_3 = t("<=") ^ t("<") ^ t(">=") ^ t(">") ^ t("==") ^ t("!=")
op_4 = t("&&") ^ t("||")
op_5 = t("=")
op_all = op_4 ^ op_3 ^ op_2 ^ op_1


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
#expr_1 = (expr_0 + op_1 + expr_0).parsecmap(rotate) ^ expr_0
#expr_2 = (expr_1 + op_2 + expr_1).parsecmap(rotate) ^ expr_1
#expr_3 = (expr_2 + op_3 + expr_2).parsecmap(rotate) ^ expr_2
#expr_4 = (expr_3 + op_4 + expr_3).parsecmap(rotate) ^ expr_3

expr_4 = (expr_0 + op_all + expr_0).parsecmap(rotate) ^ expr_0
expr = (symbol + op_5.result("let") + expr_4).parsecmap(rotate) ^ expr_4

@lexeme
@generate
def basic_type():
    b = yield symbol
    ks = yield times(langle >> sepBy(basic_type, comma) << rangle, 0, 1)
    return Type(type=b, parameters=[k[0] for k in ks])

@lexeme
@generate
def polymorphic_type():
    args = yield sepBy(symbol, comma)
    yield fatarrow
    t = yield basic_type
    t.freevars = args
    return t



@lexeme
@generate
def lambda_type():
    yield lpars
    args = yield sepBy(basic_type, comma)
    yield rpars
    yield arrow
    rt = yield basic_type
    return Type(type=rt, arguments = args)

typee = lambda_type ^ basic_type



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
def decl_header_with_parameters():
    '''Parse function header.'''
    name = yield symbol
    yield colon
    tpars = yield sepBy(basic_type, comma)
    yield fatarrow
    yield lpars
    args = yield sepBy(decl_args, comma)
    yield rpars
    yield arrow
    ret = yield decl_args
    ret.nodet = 'rtype'
    return name, args, ret, tpars

@lexeme
@generate
def decl_header():
    '''Parse function header.'''
    name = yield symbol
    yield colon
    yield lpars
    args = yield sepBy(decl_args, comma)
    yield rpars
    yield arrow
    ret = yield decl_args
    ret.nodet = 'rtype'
    return name, args, ret, None

@lexeme
@generate
def decl():
    '''Parse function declaration.'''
    name, args, ret, free = yield decl_header_with_parameters ^ decl_header
    yield lbrace
    body = yield many(expr).parsecmap(makeblock)
    yield rbrace
    return Node('decl', name, args, ret, body, free)

@lexeme
@generate
def native():
    '''Parse function declaration.'''
    yield t("native")
    name, args, ret, free = yield decl_header_with_parameters ^ decl_header
    return Node('native', name, args, ret, free)


@lexeme
@generate
def typedecl_with_alias():
    '''Parse type declaration.'''
    yield t("type")
    k = yield polymorphic_type ^ typee
    yield t("as")
    k2 = yield polymorphic_type ^ typee
    return Node('type', k, k2)

@lexeme
@generate
def typedecl():
    '''Parse type declaration.'''
    yield t("type")
    k = yield polymorphic_type ^ typee
    return Node('type', k)


imprt = t('import') >> symbol.parsecmap(lambda x: Node('import', x))

program = ignore >> many(typedecl_with_alias ^ typedecl ^ native ^ decl ^ imprt)


cached_imports = []
def resolve_imports(p, base_path=lambda x: x):
    n_p = []
    for n in p:
        if n.nodet == 'import':
            fname = n.nodes[0]
            path = ""
            while fname.startswith(".."):
                fname = fname[2:]
                path = path + "../"
            path = path + fname.replace(".", "/")
            if path not in cached_imports:
                cached_imports.append(path)
                ip = parse(base_path(path))
                n_p.extend(ip)
        else:
            n_p.append(n)
    return n_p

def parse(fname):
    txt = open(fname).read()
    p = program.parse_strict(txt)

    p = resolve_imports(p, base_path = lambda x : os.path.join(os.path.dirname(fname), "{}.p".format(x)))

    return p
