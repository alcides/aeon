from aeon.ast import *
from aeon.types import *

from functools import reduce

# =============================================================================
# Wraps the type in type abstractions
""" 
    Replaces
        (T:k => List T) -> Integer
    into
        T:k => (List T -> Integer)
"""
def wrap_typeabstractions(funty: AbstractionType, typee: Type):
    (_, type_abstractions_to_add_to_function) = extract_refinements(typee)
    function_type: Type = funty

    for (t, k) in reversed(type_abstractions_to_add_to_function):
        function_type = TypeAbstraction(t, k, function_type)
    
    return function_type

def extract_refinements(typee: Type):
    type_abstraction: Type = typee
    type_abstractions_to_add_to_function = []

    while isinstance(type_abstraction, TypeAbstraction):
        type_abstractions_to_add_to_function.append(
            (type_abstraction.name, type_abstraction.kind))
        type_abstraction = type_abstraction.type

    return (type_abstraction, type_abstractions_to_add_to_function)

# Removes every single TypeAbstraction and returns the type
def remove_tabs(self, typee):
    if isinstance(typee, BasicType):
        return typee
    elif isinstance(typee, RefinedType):
        typee.type = remove_tabs(typee.type)
    elif isinstance(typee, AbstractionType):
        typee.arg_type = remove_tabs(typee.arg_type)
        typee.return_type = remove_tabs(typee.return_type)
    elif isinstance(typee, TypeApplication):
        typee.target = remove_tabs(typee.target)
        typee.argument = remove_tabs(typee.argument)
    elif isinstance(typee, TypeAbstraction):
        typee = remove_tabs(typee.type)
    return typee

# Search for abstractions in a given type and return the list of them: [X, Y]
def search_tabs(typee):
    abstractions = []

    # Check if the BasicType is a TypeeIdentifier
    if isinstance(typee, BasicType):
        if len(typee.name) == 1:
            abstractions = [typee.name]
    
    # Check the RefinedType type
    elif isinstance(typee, RefinedType):
        abstractions = search_tabs(typee.type)
    
    # Check the AbstractionType arg_type and return_type
    elif isinstance(typee, AbstractionType):
        arg_type = search_tabs(typee.arg_type)
        return_type = search_tabs(typee.return_type)
        abstractions = arg_type + return_type
    
    # Check the TypeApplication target and argument
    elif isinstance(typee, TypeApplication):
        target = search_tabs(typee.target)
        argument = search_tabs(typee.argument)
        abstractions = target + argument
    
    # Check the name of each TypeAbstraction, progress the typee and return it
    elif isinstance(typee, TypeAbstraction):
        while isinstance(typee, TypeAbstraction):
            abstractions = abstractions + search_tabs(
                typee.name)
            typee = typee.type
        abstractions = abstractions + search_tabs(typee)
    
    return abstractions

# Englobe the typee in the tabstractions
def englobe_typeabs(ttype, tabs):
    return reduce(lambda abst, retType: TypeAbstraction(retType, star, abst),
            tabs, ttype)

def englobe_typeapps(ttype, tapps):
    return reduce(lambda target, argument: TypeApplication(target, argument),
            tapps, ttype)

# =============================================================================
# Given a type obtain its type name and its type kind
def get_type_name(typee : Type):
    if isinstance(typee, BasicType):
        return typee.name
    elif isinstance(typee, RefinedType):
        return get_type_name(typee.type)
    elif isinstance(typee, AbstractionType):
        return get_type_name(typee.return_type)
    elif isinstance(typee, TypeApplication):
        return get_type_name(typee.target)
    elif isinstance(typee, TypeAbstraction):
        return get_type_name(typee.type)
    else:
        raise Exception("Unknown type when obtaining the basic type name")

def get_type_kind(typee : Type):
    if isinstance(typee, BasicType):
        return star
    elif isinstance(typee, RefinedType):
        return star
    elif isinstance(typee, AbstractionType):
        return star
    elif isinstance(typee, TypeApplication):
        return Kind(star, get_type_kind(typee.target))
    elif isinstance(typee, TypeAbstraction):
        return get_type_kind(typee.type)
    else:
        raise Exception("Unknown type when obtaining the kind:", type(typee))

# =============================================================================
# Given the arguments of a definition, preprocess it
def preprocess_args(args):
    
    name = args[0]
    (tabs, tapps), params = (None, None), None

    # There are no tabstractions nor parameters
    if len(args) == 2:
        ttype = args[1]

    elif len(args) == 3:
        # There are tabs and/or tapps
        if isinstance(args[1], list):
            (tabs, tapps) = args[1]
        # There are params
        else:
            params = args[1]

        ttype = args[2]

    elif len(args) == 4:
        (tabs, tapps), params, ttype = args[1:]
    
    return name, (tabs, tapps), params, ttype

def create_definition_ttype(params, rtype):
    return reduce(lambda ttype, p: AbstractionType(p[0], p[1], ttype),
            params, rtype)