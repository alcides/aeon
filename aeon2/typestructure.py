import copy
import sys

from .utils import *
from .ast import Node


class Type(object):
    def copy(self):
        return copy.deepcopy(self)
        
        
def find_substitution_for(candidate, pattern, substitutions = None):
    if substitutions == None:
        substitutions = {}
    if not type(pattern) is PolyType:
        print("Wrong substitution in something that is not a pattern", pattern)
    elif not type(candidate) is type(pattern.term):
        return None
    elif type(candidate) is BasicType:
        if candidate == pattern.term:
            return {}
        elif str(pattern.term) in pattern.binders and not (pattern.term in substitutions and substitutions[pattern.term] != candidate): #?
            return {pattern.term: candidate}
        else:
            return None
    elif type(candidate) is ParametricType:
        if len(candidate.type_arguments) != len(pattern.term.type_arguments):
            return None
        subs = find_substitution_for(candidate.basic, pattern.term.basic, substitutions)
        if subs == None:
            return None
        else:
            substitutions.extend(subs)
        
        for candidate_arg, pattern_arg in zip(candidate.type_arguments, pattern.term.type_arguments):
            subs = find_substitution_for(candidate_arg, pattern_arg, substitutions)
            if subs is None:
                return None
            else:
                substitutions.extend(subs)
            
    elif type(candidate) is FunctionType:
        pass # TODO
        return None
    
        
        
class RefinedType(Type):
    def __init__(self, refinements=None):
        self.refinements = refinements or []
        
    def add_refinements(self, conds):
        self.refinements.extend(conds)
        
    def replace_vars(self, mapping):
        self.refinements = [replace_vars(n, mapping) for n in self.refinements]

        return self
        
    def str_in_refinements(self, inside):
        if self.refinements:
            return "{{ {} where {} }}".format(inside, " and ".join(map(str, self.refinements)))
        else:
            return inside

class BasicType(RefinedType):
    """
        Integer
    """
    def __init__(self, basic="Object", refinements=None, properties=None):
        super(BasicType, self).__init__(refinements)
        self.basic = basic
        self.properties = properties or []
        
    def replace_type(self, tname, ttype):
        if str(self.basic) == str(tname):
            c = ttype.copy()
            c.add_refinements(this.refinements)
            return c
        return self
        
    def get_properties(self):
        return self.properties
    
    def add_properties(self, props):
        self.properties.extend(props)
        
    def __str__(self):
        props = self.properties and " {" + "\n".join(map(str, self.properties)) + "}" or ""
        s = "{}{}".format(self.basic, props)
        return self.str_in_refinements(s)
        
    def __eq__(self, other):
        return str(self.basic) == str(other)
        
        
class ParametricType(RefinedType):
    """
        ArrayList<Integer>
    """
    def __init__(self, basic, type_arguments, properties=None, refinements=None):
        super(ParametricType, self).__init__(refinements)
        if type(basic) == str:
            basic = BasicType(basic)
        self.basic = basic
        self.type_arguments = type_arguments
        self.properties = properties or []
        
    def __str__(self):
        props = self.properties and " {" + "\n".join(map(str, self.properties)) + "}" or ""
        args = ", ".join(map(str, self.type_arguments))
        s = "{}<{}>{}".format(self.basic, args, props)
        return self.str_in_refinements(s)
        
    def get_properties(self):
        return self.properties
    
    def add_properties(self, props):
        self.properties.extend(props)
        
    def replace_vars(self, mapping):
        self.basic.replace_vars(mapping)
        return self
        
    def replace_type(self, tname, ttype):
        self.basic = self.basic.replace_type(tname, ttype)
        self.type_arguments = [ x.replace_type(tname, ttype) for x in self.type_arguments ]
        
        if type(ttype) is PolyType:
            subs = find_substitution_for(self, ttype)
            if subs != None:
                c = ttype.copy()
                c.refinements = self.refinements
                return c

        return self
        
class FunctionType(RefinedType):
    """
        (Integer, Boolean) -> String
    """
    def __init__(self, return_type, parameter_types, refinements=None):
        super(FunctionType, self).__init__(refinements)
        self.return_type = return_type
        self.parameter_types = parameter_types
        
    def __str__(self):
        args = ", ".join(map(str, self.parameter_types))
        s = "({}) -> {}".format(args, self.return_type)
        return self.str_in_refinements(s)
        
    def replace_vars(self, mapping):
        super(FunctionType, self).replace_vars(mapping)
        self.return_type.replace_vars(mapping)
        for p in self.parameter_types:
            self.return_type.replace_vars(mapping)     
        return self
        
    def replace_type(self, tname, ttype):
        self.return_type = self.return_type.replace_type(tname, ttype)
        self.parameter_types = [ x.replace_type(tname, ttype) for x in self.parameter_types ]
        
        if type(ttype) is PolyType:
            subs = find_substitution_for(ttype)
            if subs != None:
                c = ttype.copy()
                c.refinements = self.refinements
                return c

        return self

class PolyType(Type):
    """
        T => ArrayList<T>
    """
    def __init__(self, binders, term):
        self.binders = binders
        self.term = term
        
    def replace_vars(self, mapping):
        self.term.replace_vars(mapping)
        
    def get_properties(self):
        return self.term.get_properties()
        
    def add_properties(self, props):
        self.term.add_properties(props)
        
    def add_refinements(self, refs):
        self.term.add_refinements(refs)
        
    def replace_type(self, tname, ttype):
        self.term.replace_type(tname, ttype)

    def __str__(self):
        if self.binders:
            binders = ", ".join(map(str, self.binders))
            return "{} => {}".format(binders, self.term)
        else:
            return self.term


# defaults
t_v = BasicType('Void')
t_n = BasicType('Object')
t_f = BasicType('Double')
t_i = BasicType('Integer')
t_b = BasicType('Boolean')
t_s = BasicType('String')


