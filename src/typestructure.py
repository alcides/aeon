import copy
from .utils import *

class Type(object):
    def __init__(self, type="Object", arguments=None, parameters=None, conditions=None, effects=None, freevars=None):
        self.type = type
        self.arguments = arguments
        self.parameters = parameters and parameters or []
        self.freevars = freevars
        self.conditions = conditions and conditions or []
        self.effects = effects and effects or []

    def contains(self, c):
        if type(self.type) == str:
            return self.type == str(c)
        else:
            return self.type.contains(c) or \
                any([ a.contains(c) for a in  self.arguments]) or \
                any([ a.contains(c) for a in  self.parameters])

    def copy_replacing_freevar(self, free, fixed):

        def rep(target):
            if type(target) == str:
                if target == str(free):
                    T = fixed
                else:
                    T = target
            else:
                T = target.copy_replacing_freevar(free, fixed)
            return T
        new_freevars = orNone(self.freevars, lambda x: [ f for f in x if f != free ])
        if not new_freevars:
            new_freevars = None
        return Type(
            type = rep(self.type),
            arguments = orNone(self.arguments, lambda x: [ rep(e) for e in x ]),
            parameters =  orNone(self.parameters, lambda x: [ rep(e) for e in x ]),
            conditions = copy.deepcopy(self.conditions),
            effects = copy.deepcopy(self.effects),
            freevars = new_freevars
        )

    def __str__(self):
        t = str(self.type)
        if self.parameters:
            t += "<" + ", ".join(map(str, self.parameters)) + ">"
        if self.arguments != None:
            t = "({})".format(", ".join(map(str, self.arguments))) + " -> " + t
        if self.freevars != None:
            t = "{} => {}".format(",".join(map(str, self.freevars)), t)
        return t


    def __hash__(self):
        return str(self).__hash__()

    def __eq__(self, other):
        if type(other) != Type:
            return False
        if str(other) == str(self):
            return True
        return self.type == other.type and \
            self.arguments == other.arguments and \
            len(self.parameters) == len(other.parameters) and \
            all([ a == b for (a,b) in zip(self.parameters, other.parameters) ])

    def polymorphic_matches(self, other, tcontext, mapping = None):
        """ Returns mapping of freevars used to convert from self to other """
        if mapping == None:
            mapping = {}
        if not self.freevars:
            if self == other:
                return mapping
            else:
                return None
        for fv in self.freevars:
            for c in tcontext.types:
                mapping[fv] = c
                tconcrete = self.copy_replacing_freevar(fv, c)
                mp = tconcrete.polymorphic_matches(other, tcontext, mapping)
                if mp != None:
                    return mp
        return None


    def polymorphic_fill(self, mapping):
        """ Returns type with freevars mapped """
        t = self
        for k in mapping:
            t = t.copy_replacing_freevar(k, mapping[k])
        return t

# defaults
t_v = Type('Void')
t_n = Type('Object')
t_i = Type('Integer')
t_b = Type('Boolean')
t_f = Type('Float')
