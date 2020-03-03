from aeon.types import *


def extract_refinements(typee: Type):
    type_abstraction: Type = typee
    type_abstractions_to_add_to_function = []
    while isinstance(type_abstraction, TypeAbstraction):
        type_abstractions_to_add_to_function.append(
            (type_abstraction.name, type_abstraction.kind))
        type_abstraction = type_abstraction.type
    return (type_abstraction, type_abstractions_to_add_to_function)


def wrap_typeabstractions(funty: AbstractionType, typee: Type):
    """ Replaces
            (T:k => List T) -> Integer
        into
            T:k => (List T -> Integer)
    """
    (_, type_abstractions_to_add_to_function) = extract_refinements(typee)

    function_type: Type = funty
    for (t, k) in reversed(type_abstractions_to_add_to_function):
        function_type = TypeAbstraction(t, k, function_type)
    return function_type
