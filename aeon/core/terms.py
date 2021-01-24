from aeon.core.types import Type


class Term(object):
    pass


class Literal(Term):
    value: object
    type: Type

    def __init__(self, value, type: Type):
        self.value = value
        self.type = type

    def __str__(self):
        return u"({}::{})".format(self.value, self.type)

    def __eq__(self, other):
        return (isinstance(other, Literal) and self.value == other.value
                and self.type == other.type)


class Var(Term):
    name: str

    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return u"{}".format(self.name)

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name


class Application(Term):
    fun: Term
    arg: Term

    def __init__(self, fun: Term, arg: Term):
        self.fun = fun
        self.arg = arg

    def __str__(self):
        return u"({} {})".format(self.fun, self.arg)

    def __eq__(self, other):
        return (isinstance(other, Application) and self.fun == other.fun
                and self.arg == other.arg)


class Abstraction(Term):
    var_name: str
    body: Term

    def __init__(self, var_name: str, body: Term):
        self.var_name = var_name
        self.body = body

    def __str__(self):
        return u"(\\{} -> {})".format(self.var_name, self.body)

    def __eq__(self, other):
        return (isinstance(other, Abstraction)
                and self.var_name == other.var_name
                and self.body == other.body)


class Let(Term):
    var_name: str
    var_value: Term
    body: Term

    def __init__(self, var_name: str, var_value: Term, body: Term):
        self.var_name = var_name
        self.var_value = var_value
        self.body = body

    def __str__(self):
        return u"(let {} = {} in {})".format(self.var_name, self.var_value,
                                             self.body)

    def __eq__(self, other):
        return (isinstance(other, Let) and self.var_name == other.var_name
                and self.var_value == other.var_value
                and self.body == other.body)


class Rec(Term):
    var_name: str
    var_type: Type
    var_value: Term
    body: Term

    def __init__(self, var_name: str, var_type: Type, var_value: Term,
                 body: Term):
        self.var_name = var_name
        self.var_type = var_type
        self.var_value = var_value
        self.body = body

    def __str__(self):
        return u"(let {} : {} = {} in {})".format(self.var_name, self.var_type,
                                                  self.var_value, self.body)

    def __eq__(self, other):
        return (isinstance(other, Rec) and self.var_name == other.var_name
                and self.var_type == other.var_type
                and self.var_value == other.var_value
                and self.body == other.body)


class If(Term):
    cond: Term
    then: Term
    otherwise: Term

    def __init__(self, cond: Term, then: Term, otherwise: Term):
        self.cond = cond
        self.then = then
        self.otherwise = otherwise

    def __str__(self):
        return u"(if {} then {} else {})".format(self.cond, self.then,
                                                 self.otherwise)

    def __eq__(self, other):
        return (isinstance(other, If) and self.cond == other.cond
                and self.then == other.then
                and self.otherwise == other.otherwise)
