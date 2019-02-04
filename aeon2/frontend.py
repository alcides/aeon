import re
import os
import os.path
import copy
from parsec import *

from .ast import *
from .typestructure import *

ext = 'ae'

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
bangcolon = t('!:')
pipe = t('|')
comma = t(',')
arrow = t('->')
fatarrow = t('=>')
hole = t('…').result(Hole())
true = t('true').result(Literal(True, type=t_b))
false = t('false').result(Literal(False, type=t_b))
null = t('null').result(Literal(None, type=t_n))
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
            return Literal(int(x), type=copy.deepcopy(t_i))
        else:
            return Literal(float(x), type=copy.deepcopy(t_f))

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
    name = yield symbol
    yield lpars
    args = yield sepBy(expr, comma)
    yield rpars
    v = 0
    if name.split(".")[-1].isdigit():
        v = int(name.split(".")[-1])
        name = ".".join(name.split(".")[:-1]) # remove .1
    return Invocation(name, args, version=v)



@lexeme
@generate
def expr_wrapped():
    o = yield expr
    return o

# helper
rotate = lambda x: Operator(x[0][1], x[0][0], x[1])
makeblock = lambda xs: Block(*xs)

symbol_e = symbol.parsecmap(lambda x: Atom(x))
block = (lbrace >> many(expr_wrapped)  << rbrace).parsecmap(makeblock)

@lexeme
@generate
def lambd():
    yield lpars
    args = yield sepBy(symbol + (colon >> basic_type), comma)
    yield rpars
    yield arrow
    e = yield block ^ expr
    return LambdaExpression(map(lambda p: Argument(name=p[0], type=p[1]), args), e)


@lexeme
@generate
def let():
    s = yield symbol
    coerc = yield (colon ^ bangcolon) ^ t("")
    if coerc:
        typ = yield typee
        coerced = True
    else:
        typ = None
        coerced = False
    yield op_5
    definition = yield expr_4
    return Let(s, definition, type=typ, coerced=coerced)


atom = true ^ false ^ null ^ number() ^ invocation ^ symbol_e ^ (lpars >> expr_wrapped << rpars) ^ lambd ^ hole
expr_0 = (op_2 + atom).parsecmap(lambda x:Operator(*x)) ^ atom
#expr_1 = (expr_0 + op_1 + expr_0).parsecmap(rotate) ^ expr_0
#expr_2 = (expr_1 + op_2 + expr_1).parsecmap(rotate) ^ expr_1
#expr_3 = (expr_2 + op_3 + expr_2).parsecmap(rotate) ^ expr_2
#expr_4 = (expr_3 + op_4 + expr_3).parsecmap(rotate) ^ expr_3

expr_4 = (expr_0 + op_all + expr_0).parsecmap(rotate) ^ expr_0
expr = let ^ expr_4


@lexeme
@generate
def basic_type():
    b = yield symbol
    ks = yield times(langle >> sepBy(basic_type, comma) << rangle, 0, 1)
    if ks:
        return ParametricType(basic=b, type_arguments=ks[0])
    else:
        return BasicType(basic=b)

@lexeme
@generate
def polymorphic_type():
    args = yield sepBy(symbol, comma)
    yield fatarrow
    t = yield basic_type
    return PolyType(binders=args, term=t)

@lexeme
@generate
def lambda_type():
    yield lpars
    args = yield sepBy(basic_type, comma)
    yield rpars
    yield arrow
    rt = yield basic_type
    return FunctionType(return_type=rt, parameter_types=args)
    
@lexeme
@generate
def refined_type():
    yield t("{")
    basic_t = yield basic_type
    yield t("where")
    ls = yield sepBy(expr, t("and"))
    yield t("}")
    rt = BasicType(basic=basic_t, refinements = ls)
    return rt
    

typee = lambda_type ^ basic_type ^ refined_type



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
    return Argument(arg, typ)


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
def where():
    yield t("where")
    yield t("[")
    ls = yield sepBy(expr, t("and"))
    yield t("]")
    return ls
    
@generate
def tracked_arg():
    arg = yield symbol
    yield colon
    typ = yield typee
    trackedBy = yield (t("trackedBy") >> symbol ) ^ t("")
    return Argument( arg, typ, trackedBy)
    
@lexeme
@generate
def tracked_args():
    yield t("{")
    ls = yield sepBy(tracked_arg, t(","))
    yield t("}")
    return ls

@lexeme
@generate
def effects():
    yield t("with")
    yield t("[")
    ls = yield sepBy(expr, t("and"))
    yield t("]")
    return ls

@lexeme
@generate
def decl_native_shared():
    name, args, ret, tpars = yield decl_header_with_parameters ^ decl_header
    refinements = yield where ^ t("")
    effs = yield effects ^ t("")
    if not refinements:
        refinements = None
    if not effs:
        effs = None
    return name, args, ret, tpars, refinements, effs

@lexeme
@generate
def decl():
    '''Parse function declaration.'''
    name, args, ret, tpars, refinements, effs = yield decl_native_shared
    yield lbrace
    body = yield many(expr).parsecmap(makeblock)
    yield rbrace
    return FunctionDecl(name, args, ret, tpars, refinements, effs, body)

@lexeme
@generate
def native():
    '''Parse function declaration.'''
    yield t("native")
    name, args, ret, free, refinements, effs = yield decl_native_shared
    return FunctionDecl(name, args, ret, free, refinements, effs)


@lexeme
@generate
def typedecl():
    '''Parse type declaration.'''
    yield t("type")
    imported = yield polymorphic_type ^ typee
    properties = yield tracked_args ^ t("")
    refinements = yield where ^ t("")
    alias = yield (t("as") >> (polymorphic_type ^ typee)) ^ t("")
    return TypeDecl(imported, alias, properties, refinements)

imprt = t('import') >> symbol.parsecmap(lambda x: Import(x))

program = ignore >> many(typedecl ^ native ^ imprt ^ decl)


cached_imports = []
def resolve_imports(p, base_path=lambda x: x):
    n_p = []
    for n in p:
        if type(n) is Import:
            fname = n.name
            path = ""
            while fname.startswith(".."):
                fname = fname[2:]
                path = path + "../"
            path = path + fname.replace(".", "/")
            path = os.path.realpath(base_path(path))
            if path not in cached_imports:
                cached_imports.append(path)
                ip = parse(path)
                n_p.extend(ip.declarations)
        else:
            n_p.append(n)
    return n_p

def parse(fname):
    txt = open(fname).read()
    p = program.parse_strict(txt)
    p = resolve_imports(p, base_path = lambda x : os.path.join(os.path.dirname(fname), "{}.{}".format(x, ext)))
    return Program(p)