import copy
import sys
from .utils import *
from .ast import Node

class Type(object):
    def __init__(self, type="Object", arguments=None, parameters=None, conditions=None, effects=None, freevars=None):
        self.type = type
        self.arguments = arguments
        self.parameters = parameters and parameters or []
        self.freevars = freevars
        self.conditions = conditions and conditions or []
        self.preconditions = []
        self.effects = effects and effects or []


    def replace(self, c, names, argnames=None):
        if type(c) == list:
            return any([ self.replace(n, names, argnames) for n in c ])
        if type(c) != Node:
            return False
        status = False
        if c.nodet == 'atom':
            if argnames:
                if c.nodes[0] in argnames:
                    c.nodes = list(c.nodes)
                    c.nodes[0] = "__argument_{}".format(argnames.index(c.nodes[0]))
            if c.nodes[0] in names:
                c.nodes = list(c.nodes)
                c.nodes[0] = "__return_{}".format(names.index(c.nodes[0]))
                status = True
        else:
            status = any([ self.replace(n, names, argnames) for n in c.nodes ])
        return status

    def set_conditions(self, conds, names, argnames=[]):
        self.preconditions = []
        self.conditions = []
        if conds:
            for c in conds:
                if self.replace(c, names, argnames):
                    self.conditions.append(c)
                else:
                    self.preconditions.append(c)
                    
    def set_effects(self, effs, names, argnames=[]):
        self.effects = [ ]
        if effs:
            for eff in effs:
                self.replace(eff, names, argnames)
                self.effects.append(eff)

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
        if self.conditions:
            t += " where " + " and ".join([ str(e) for e in self.conditions])
        if self.preconditions:
            t += " pre-where " + " and ".join([ str(e) for e in self.preconditions])
        if self.effects:
            t += " with " + " and ".join([ str(e) for e in self.effects])
        return t

    def __repr__(self):
        d = {}
        if self.freevars != None:
            d['freevars'] = self.freevars
        if self.type != None:
            d['basic'] = self.type
        if self.parameters:
            d['parameters'] = self.parameters
        if self.arguments != None:
            d['arguments'] = self.arguments
        if self.conditions:
            d['conditions'] = self.conditions
        if self.effects:
            d['effects'] = self.effects

        return repr(d)

    def __hash__(self):
        return str(self.type).__hash__()

    def __eq__(self, other):
        if type(other) == str:
            return str(self) == str(other)
        if type(other) != Type:
            return False
        
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
t_f = Type('Double')
t_i = Type('Integer')
t_b = Type('Boolean')
