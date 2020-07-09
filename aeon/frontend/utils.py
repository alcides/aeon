from aeon.ast import *
from aeon.types import *

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
        raise Exception("Unknown type when obtaining the kind")