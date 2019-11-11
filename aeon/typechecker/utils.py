from ..types import Type, BasicType, RefinedType


def flatten_refined_type(t: Type):
    if isinstance(t, BasicType):
        return t
    if isinstance(t, RefinedType):
        return flatten_refined_type(t.type)
    raise Exception("Error flattening type: {} ({})".format(t, type(t)))
