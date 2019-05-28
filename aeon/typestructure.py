import copy
import sys

from .utils import *
from .ast import Node
from .prettyprinter import prettyprint

class Type(object):
    def __init__(self, basic="Object", lambda_parameters=None, type_arguments=None, conditions=None, effects=None, binders=None, preconditions=None, properties=None):
        self.type = basic 
        self.lambda_parameters = lambda_parameters
        self.type_arguments = type_arguments and type_arguments or []
        self.binders = binders
        self.conditions = conditions and conditions or []
        self.preconditions = preconditions and preconditions or []
        self.effects = effects and effects or []
        self.properties = properties and properties or []

        self.propagate_binders()

    def is_function(self):
        return self.lambda_parameters != None

    def consolidate(self):
        if type(self.type) == Type and self.lambda_parameters==None:
            o = self.type
            self.type = o.type
            if o.conditions:
                self.conditions.extend(o.conditions)
            self.consolidate()

    def propagate_binders(self, t=None):
        if self.binders:
            if t == None:
                self.propagate_binders(self.type)
                if self.lambda_parameters:
                    for arg in self.lambda_parameters:
                        self.propagate_binders(arg)
                if self.type_arguments:
                    for par in self.type_arguments:
                        self.propagate_binders(par)
            elif type(t) == Type:
                t.binders = []
                for a in (t.lambda_parameters or []) + (t.type_arguments or []):
                    for fv in self.binders:
                        if a == fv and fv not in t.binders:
                            t.binders.append(fv)
                if not t.binders:
                    t.binders = None


    def replace(self, c, names, argnames=None):
        if type(c) == list:
            return any([ self.replace(n, names, argnames) for n in c ])
        if type(c) != Node:
            return False
        status = False
        if c.nodet in ['atom']:
            atom = c.nodes[0].split(".")[0]
            remaining = '.' in c.nodes[0] and ("__index__" + c.nodes[0].split(".")[-1]) or ''
            if argnames:
                if atom in argnames:
                    c.nodes = list(c.nodes)
                    c.nodes[0] = "__argument_{}{}".format(argnames.index(atom), remaining)
            if atom in names:
                c.nodes = list(c.nodes)
                c.nodes[0] = "__return_{}{}".format(names.index(atom), remaining)
                status = True
            if atom.startswith("__return_"):
                status = True
        else:
            status = any([ self.replace(n, names, argnames) for n in c.nodes ])
        return status


    def depends_on(self, c, prefix):
        if type(c) == list:
            return any([ self.depends_on(n, prefix) for n in c ])
        if type(c) != Node:
            return False
        if c.nodet in ['atom']:
            if c.nodes[0].startswith(prefix):
                return True
            else:
                return False
        else:
            status = any([ self.depends_on(n, prefix) for n in c.nodes ])
        return status

    def set_properties(self, ps):
        self.properties = ps

    def set_conditions(self, conds, names, argnames=[]):
        self.preconditions = []
        self.conditions = []
        if conds:
            for c in conds:
                self.add_condition(c, names, argnames)


    def add_condition(self, c, names=[], argnames=[], skip_rename=False):

        if not skip_rename:
            self.replace(c, names, argnames)
        if self.depends_on(c, '__return_0'):
            if c not in self.conditions:
                self.conditions.append(c)
                if not self.depends_on(c, '__argument'):
                    if self.lambda_parameters:
                        if type(self.type) == str:
                            self.type = Type(self.type)
                        self.type.add_condition(c, skip_rename=True)
        else:
            if c not in self.preconditions:
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
                any([ a.contains(c) for a in self.lambda_parameters]) or \
                any([ a.contains(c) for a in self.type_arguments])

    def copy(self):
        return copy.copy(self)

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
        new_binders = orNone(self.binders, lambda x: [ f for f in x if f != free ])
        if not new_binders:
            new_binders = None
        return Type(
            basic = rep(self.type),
            lambda_parameters = orNone(self.lambda_parameters, lambda x: [ rep(e) for e in x ]),
            type_arguments =  orNone(self.type_arguments, lambda x: [ rep(e) for e in x ]),
            conditions = copy.deepcopy(self.conditions),
            preconditions = copy.deepcopy(self.preconditions),
            effects = copy.deepcopy(self.effects),
            binders = new_binders,
            properties = self.properties
        )

    def __str__(self):
        t = str(self.type)
        if self.type_arguments:
            t += "<" + ", ".join(map(str, self.type_arguments)) + ">"
        if self.lambda_parameters != None:
            t = "({})".format(", ".join(map(lambda x: "{" + str(x) + "}", self.lambda_parameters))) + " -> {" + t + "}"
        if self.binders != None:
            t = "{} => {}".format(",".join(map(str, self.binders)), t)
        if self.properties:
            t += "{ " + ", ".join([ prettyprint(e) for e in self.properties]) + "} "
        if self.conditions:
            t += " where " + " and ".join([ prettyprint(e) for e in self.conditions])
        if self.preconditions:
            t += " pre-where " + " and ".join([ prettyprint(e) for e in self.preconditions])
        if self.effects:
            t += " with " + " and ".join([ prettyprint(e) for e in self.effects])

        elif hasattr(self, 'refined') and False:
            if hasattr(self, 'refined_value'):
                t += "<{}={}>".format(str(self.refined), str(self.refined_value))
            else:
                t += "<{}>".format(str(self.refined))

        return t

    def __repr__(self):
        d = {}
        if self.binders != None:
            d['binders'] = self.binders
        if self.type != None:
            d['basic'] = self.type
        if self.type_arguments:
            d['parameters'] = self.type_arguments
        if self.lambda_parameters != None:
            d['arguments'] = self.lambda_parameters
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

        self.consolidate()
        other.consolidate()

        return self.type == other.type and \
            self.lambda_parameters == other.lambda_parameters and \
            len(self.type_arguments) == len(other.type_arguments) and \
            all([ a == b for (a,b) in zip(self.type_arguments, other.type_arguments) ])

    def polymorphic_matches(self, other, tcontext, mapping = None):
        """ Returns mapping of binders used to convert from self to other """
        if mapping == None:
            mapping = {}
        if not self.binders:
            if self == other:
                return mapping
            else:
                return None
        for fv in self.binders:
            for c in tcontext.types:
                mapping[fv] = c
                tconcrete = self.copy_replacing_freevar(fv, c)
                mp = tconcrete.polymorphic_matches(other, tcontext, mapping)
                if mp != None:
                    return mp
        return None


    def polymorphic_fill(self, mapping):
        """ Returns type with binders mapped """
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
t_s = Type('String')
