import copy
import sys

from .ast import *


class TypeException(Exception):
    def __init__(self,
                 name,
                 description="",
                 given=None,
                 expected=None,
                 *args,
                 **kwargs):
        super(TypeException, self).__init__(name, description)
        self.expected = expected
        self.given = given


class TypingContext(object):
    def __init__(self):
        self.type_aliases = {}
        self.variables = {}
        self.type_variables = {}
        self.basic_types = []

    def setup(self):
        from .stdlib import get_all_builtins, get_builtin_type
        for name in get_all_builtins():
            self.variables[name] = get_builtin_type(name)

        self.type_variables = {
            t_v: star,
            t_i: star,
            t_f: star,
            t_o: star,
            t_b: star,
            t_s: star,
            bottom: star
        }
        # As of Python3, dict_keys is not copyable, so a list is required
        self.basic_types = list(self.type_variables.keys())

    def add_var(self, n, t):
        if type(t) is BasicType:
            if t.name in self.type_aliases:
                t = self.type_aliases[t.name]
        self.variables[n] = t

    def add_type_var(self, n, k):
        self.type_variables[n] = k

    def is_basic_type(self, type):
        for t in self.basic_types:
            if t.name == type.name:
                return True
        return False

    def with_var(self, name, type):
        new_ctx = copy.deepcopy(self)
        new_ctx.add_var(name, type)
        return new_ctx

    def with_type_var(self, name, kind):
        new_ctx = copy.deepcopy(self)
        new_ctx.add_type_var(name, kind)
        return new_ctx


class Kind(object):
    def __init__(self, k1=None, k2=None):
        self.k1 = k1
        self.k2 = k2

    def is_star(self):
        return self.k1 == None and self.k2 == None

    def __eq__(self, o):
        if type(o) != Kind:
            return False
        if self.is_star() and o.is_star():
            return True
        return self.k1 == o.k1 and self.k2 == o.k2
    
    def __repr__(self):
        return str(self) 
    
    def __str__(self):
        if self.is_star():
            return "*"
        return "{} => {}".format(self.k1, self.k2)


star = Kind()


class Type(object):
    def copy(self):
        return copy.deepcopy(self)

    def __repr__(self):
        return str(self)


class BasicType(Type):
    """ Integer | Boolean | B """

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name

    def __hash__(self):
        return hash(self.name)


class AbstractionType(Type):
    """ x:T -> U """

    def __init__(self, arg_name, arg_type, return_type):
        self.arg_name = arg_name
        self.arg_type = arg_type
        self.return_type = return_type

    def __str__(self):
        return "{}:{} -> ({}):".format(self.arg_name, self.arg_type,
                                       self.return_type)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.arg_name == o.arg_name \
            and self.arg_type == o.arg_type \
            and self.return_type == o.return_type


class RefinedType(Type):
    """ x:T where U """

    def __init__(self, name, type, cond):
        self.name = name
        self.type = type
        self.cond = cond

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name \
            and self.type == o.type \
            and self.cond == o.cond

    def __str__(self):
        return "{{ {}:{} where {} }}".format(self.name, self.type, self.cond)


class TypeAbstraction(Type):
    """T:k => U"""

    def __init__(self, name, kind, type):
        self.name = name
        self.kind = kind
        self.type = type

    def __str__(self):
        return "{}:{} => {}".format(self.name, self.kind, self.type)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.name == o.name \
            and self.kind == o.kind \
            and self.type == o.type


class TypeApplication(Type):
    """ T U """

    def __init__(self, target, argument):
        self.target = target
        self.argument = argument

    def __str__(self):
        return "({} {})".format(self.target, self.argument)

    def __eq__(self, o):
        return type(self) == type(o) \
            and self.target == o.target \
            and self.argument == o.argument


# defaults
t_v = BasicType('Void')
t_t = BasicType('Top')
t_o = BasicType('Object')
t_f = BasicType('Double')
t_i = BasicType('Integer')
t_b = BasicType('Boolean')
t_s = BasicType('String')
bottom = BasicType('Bottom')