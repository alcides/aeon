from __future__ import annotations

import pytest

from aeon.core.terms import Literal, Var
from aeon.core.types import TypeConstructor, t_int, t_float, t_string, t_bool
from aeon.synthesis_grammar.grammar import create_literals_nodes, create_var_node, extract_all_types
from aeon.prelude.prelude import native_types
from aeon.utils.name import Name

types_and_values = [
    (t_bool, True),
    (t_int, 5),
    (t_float, 5.0),
    (t_string, "hello"),
]


@pytest.mark.parametrize("ty,val", types_and_values)
def test_core_literal(ty, val):
    type_info = extract_all_types([ty] + list(map(TypeConstructor, native_types)))
    literal = create_literals_nodes(type_info, [ty])[0]
    assert literal(val).get_core() == Literal(val, ty)


vars_to_test = [(Name("x", 5), t_int), (Name("t", 8), t_bool)]


@pytest.mark.parametrize("name,ty", vars_to_test)
def test_core_var(name, ty):
    type_info = extract_all_types([ty])
    node = create_var_node(name, ty, type_info[ty])

    match node().get_core():
        case Var(var_name):
            assert var_name == name
        case _:
            assert False, f"Expected Var, got {node().get_core()}"
