import copy
import sys

from .utils import *
from .ast import Node


class TypingContext(object):
    def __init__(self):
        self.type_aliases = {}
        self.variables = {}
        self.type_variables = {}
        self.basic_types = []

    def setup(self):
        self.variables = {
            t_v: star,
            t_i: star,
            t_f: star,
            t_o: star,
            t_b: star,
            t_s: star,
        }
        # As of Python3, dict_keys is not copyable, so a list is required
        self.basic_types = list(self.variables.keys())

    def add_var(self, n, t):
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
        return self.k1 == self.k2

    def __str__(self):
        if self.is_star():
            return "*"
        return "{} => {}".format(self.k1, self.k2)


star = Kind()


class Type(object):
    def copy(self):
        return copy.deepcopy(self)


class BasicType(Type):
    """ Integer | Boolean | B """

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name


class ArrowType(Type):
    """ x:T -> U """

    def __init__(self, x, t1, t2):
        self.name = x
        self.type = t1
        self.argument = t2

    def __str__(self):
        return "{}:{} -> {}".format(self.name, self.type, self.argument)


class RefinedType(Type):
    """ x:T -> U """

    def __init__(self, x, t, cond):
        self.name = x
        self.type = t
        self.cond = cond

    def __str__(self):
        return "{{ {}:{} where {} }}".format(self.name, self.type, self.cond)


class TypeAbstraction(Type):
    """T:k => U"""

    def __init__(self, x, k, type):
        self.name = x
        self.kind = k
        self.type = type

    def __str__(self):
        return "{}:{} => {}".format(self.name, self.kind, self.type)


class TypeApplication(Type):
    """ T U """

    def __init__(self, type1, type2):
        self.target = type1
        self.argument = type2

    def __str__(self):
        return "({} {})".format(self.target, self.argument)


# defaults
t_v = BasicType('Void')
t_o = BasicType('Object')
t_f = BasicType('Double')
t_i = BasicType('Integer')
t_b = BasicType('Boolean')
t_s = BasicType('String')
