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


class Var(Term):
    name: str

    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return u"{}".format(self.name)


class Application(Term):
    fun: Term
    arg: Term

    def __init__(self, fun: Term, arg: Term):
        self.fun = fun
        self.arg = arg

    def __str__(self):
        return u"({} {})".format(self.fun, self.arg)


class Abstraction(Term):
    var_name: str
    var_type: Type
    body: Term

    def __init__(self, var_name: str, var_type: Type, body: Term):
        self.var_name = var_name
        self.var_type = var_type
        self.body = body

    def __str__(self):
        return u"(\\{}:{} -> {})".format(self.var_name, self.var_type,
                                         self.body)


class Let(Term):
    var_name: str
    var_value: Term
    body: Term

    def __init__(self, var_name, var_value, body):
        self.var_name = var_name
        self.var_value = var_value
        self.body = body

    def __str__(self):
        return u"(let {} = {} in {})".format(self.var_name, self.var_value,
                                             self.body)


class If(Term):
    cond: Term
    then: Term
    otherwise: Term

    def __init__(self, cond, then, otherwise):
        self.cond = cond
        self.then = then
        self.otherwise = otherwise

    def __str__(self):
        return u"(if {} then {} else {})".format(self.cond, self.then,
                                                 self.otherwise)
