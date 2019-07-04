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
        regex(r'(0|[1-9][0-9]*)([.][0-9]+)?([eE][+-]?[0-9]+)?')).parsecmap(fa)


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
            |
            regex(r'u[0-9a-fA-F]{4}').parsecmap(lambda s: chr(int(s[1:], 16))))

    return string_part() | string_esc()


@lexeme
@generate
def quoted():
    '''Parse quoted string.'''
    yield string('"')
    body = yield many(charseq())
    yield string('"')
    return ''.join(body)


@lexeme
@generate
def abstraction():
    yield t("\\")
    args = yield sepBy(symbol + (t(":") >> basic_type), t(","))
    yield arrow
    e = yield expr
    return Abstraction(map(lambda p: Argument(name=p[0], type=p[1]), args), e)


@lexeme
@generate
def application():
    target = yield expr_wrapped
    yield t("(")
    arguments = yield sepBy(expr, t(","))
    yield t(")")
    return Application(target, arguments)


@lexeme
@generate
def ite():
    yield t("if")
    c = yield expr_wrapped
    yield t("then")
    then = yield expr_wrapped
    yield t("else")
    otherwise = yield expr
    return If(c, then, otherwise)


var = symbol.parsecmap(lambda x: Var(x))
literal = true ^ false ^ null ^ number() ^ quoted
expr = ite ^ literal ^ abstraction ^ application ^ var
expr_wrapped = literal ^ var ^ t("(") >> expr << t(")")

#atom = true ^ false ^ null ^ number() ^ invocation ^ symbol_e ^ (lpars >> expr_wrapped << rpars) ^ lambd ^ hole
#expr_0 = (op_2 + atom).parsecmap(lambda x:Operator(*x)) ^ atom
#expr_1 = (expr_0 + op_1 + expr_0).parsecmap(rotate) ^ expr_0
#expr_2 = (expr_1 + op_2 + expr_1).parsecmap(rotate) ^ expr_1
#expr_3 = (expr_2 + op_3 + expr_2).parsecmap(rotate) ^ expr_2
#expr_4 = (expr_3 + op_4 + expr_3).parsecmap(rotate) ^ expr_3

#expr_4 = (expr_0 + op_all + expr_0).parsecmap(rotate) ^ expr_0
#expr = let ^ expr_4


@lexeme
@generate
def basic_type():
    b = yield symbol
    return BasicType(b)


@lexeme
@generate
def arrow_type():
    yield t("(")
    x = yield symbol
    yield t(":")
    t1 = yield typee
    yield t(")")
    yield arrow
    t2 = yield typee
    return ArrowType(x, t1, t2)


@lexeme
@generate
def refined_type():
    yield t("{")
    x = yield symbol
    yield t(":")
    ty = yield typee
    yield t("where")
    cond = yield expr
    yield t("}")
    return RefinedType(x, ty, cond)


@lexeme
@generate
def type_abstraction():
    yield t("(")
    x = yield symbol
    yield t(":")
    k = yield kind
    yield t(")")
    yield fatarrow
    ty = yield typee
    return TypeAbstraction(x, k, ty)


@lexeme
@generate
def type_application():
    yield t("(")
    t1 = yield typee
    t2 = yield typee
    yield t(")")
    return TypeApplication(t1, t2)


@lexeme
@generate
def kind_rec():
    yield t("(")
    a = yield kind
    yield fatarrow
    b = yield kind
    yield t(")")
    return Kind(a, b)


kind = kind_rec ^ t("*").result(Kind())
typee = type_abstraction ^ arrow_type ^ type_application ^ refined_type ^ basic_type


@lexeme
@generate
def topleveldef():
    """ Top Level Definition: name : type = expr """
    name = yield symbol
    yield t(":")
    type_ = yield typee
    yield t("=")
    body = yield expr
    return Definition(name, type_, body)


@lexeme
@generate
def typealias():
    '''Parse type alias.'''
    yield t("type")
    imported = yield symbol
    alias = yield (t("=") >> typee)
    return TypeAlias(imported, alias)


imprt = t('import') >> symbol.parsecmap(lambda x: Import(x))

program = ignore >> many(typealias ^ topleveldef ^ imprt)

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
    p = resolve_imports(p,
                        base_path=lambda x: os.path.join(
                            os.path.dirname(fname), "{}.{}".format(x, ext)))
    return Program(p)
