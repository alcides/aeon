import copy
import sys

from .utils import *
from .ast import Node


class Kind(object):
    def __init__(self, k1=None, k2=None):
        self.k1 = None
        self.k2 = None

    def is_star(self):
        return self.k1 == None and self.k2 == None

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
        self.x = x
        self.t1 = t1
        self.t2 = t2

    def __str__(self):
        return "{}:{} -> {}".format(self.x, self.t1, self.t2)


class RefinedType(Type):
    """ x:T -> U """

    def __init__(self, x, t, cond):
        self.x = x
        self.t = t
        self.cond = cond

    def __str__(self):
        return "{{ {}:{} where {} }}".format(self.x, self.t, self.cond)


class TypeAbstraction(Type):
    """T:k => U"""

    def __init__(self, x, k, type):
        self.x = x
        self.kind = k
        self.type = type

    def __str__(self):
        return "{}:{} => {}".format(self.x, self.kind, self.type)


class TypeApplication(Type):
    """ T U """

    def __init__(self, type1, type2):
        self.target = type1
        self.argument = type2

    def __str__(self):
        return "({} {})".format(self.target, self.argument)


# defaults
t_v = BasicType('Void')
t_n = BasicType('Object')
t_f = BasicType('Double')
t_i = BasicType('Integer')
t_b = BasicType('Boolean')
t_s = BasicType('String')
