from aeon.core.types import AbstractionType, BaseType
from aeon.synthesis_grammar.grammar import get_attribute_type_name


def test_abstract_type_name():
    abstract_ty = AbstractionType("x", BaseType("Int"), AbstractionType("y", BaseType("Float"), BaseType("String")))
    assert get_attribute_type_name(abstract_ty) == "t_Int_t_Float_t_String"


# TODO more tests
