import copy
import sys
from .utils import *
from .ast import Node
from .prettyprinter import prettyprint

class Type(object):
    def __init__(self, type="Object", arguments=None, parameters=None, conditions=None, effects=None, freevars=None, preconditions=None):
        self.type = type
        self.arguments = arguments
        self.parameters = parameters and parameters or []
        self.freevars = freevars
        self.conditions = conditions and conditions or []
        self.preconditions = preconditions and preconditions or []
        self.effects = effects and effects or []
        
        self.propagate_freevars()

    def propagate_freevars(self, t=None):
        if self.freevars:
            if t == None:
                self.propagate_freevars(self.type)
                if self.arguments:
                    for arg in self.arguments:
                        self.propagate_freevars(arg)
                if self.parameters:
                    for par in self.parameters:
                        self.propagate_freevars(par)
            elif type(t) == Type:
                t.freevars = []
                for a in (t.arguments or []) + (t.parameters or []):
                    for fv in self.freevars:
                        if a == fv and fv not in t.freevars:
                            t.freevars.append(fv)
                if not t.freevars:
                    t.freevars = None


    def replace(self, c, names, argnames=None):
        if type(c) == list:
            return any([ self.replace(n, names, argnames) for n in c ])
        if type(c) != Node:
            return False
        status = False
        if c.nodet == 'atom':
            atom = c.nodes[0].split(".")[0]
            remaining = '.' in c.nodes[0] and ("__index__" + c.nodes[0].split(".")[-1]) or ''
            if argnames:
                if atom in argnames:
                    c.nodes = list(c.nodes)
                    c.nodes[0] = "__argument_{}{}".format(argnames.index(atom), remaining)
                    status = True
            if atom in names:
                c.nodes = list(c.nodes)
                c.nodes[0] = "__return_{}{}".format(names.index(atom), remaining)
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

    def copy(self):
        return copy.deepcopy(self)

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
            preconditions = copy.deepcopy(self.preconditions),
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
            t += " where " + " and ".join([ prettyprint(e) for e in self.conditions])
        if self.preconditions:
            t += " pre-where " + " and ".join([ prettyprint(e) for e in self.preconditions])
        if self.effects:
            t += " with " + " and ".join([ prettyprint(e) for e in self.effects])
        if hasattr(self, 'refined'):
            t += "{{ {} }}".format(str(self.refined))
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
