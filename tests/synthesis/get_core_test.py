from __future__ import annotations

import pytest

from aeon.core.terms import Literal, Var
from aeon.core.types import BaseType, t_int, t_float, t_string, t_bool
from aeon.synthesis_grammar.grammar import create_literals_nodes, create_var_node, extract_all_types
from aeon.prelude.prelude import native_types

types_and_values = [
    (t_bool, True),
    (t_int, 5),
    (t_float, 5.0),
    (t_string, "hello"),
]


@pytest.mark.parametrize("ty,val", types_and_values)
def test_core_literal(ty, val):
    type_info = extract_all_types([ty] + list(map(BaseType, native_types)))
    literal = create_literals_nodes(type_info, [ty])[0]
    assert literal(val).get_core() == Literal(val, ty)


vars_to_test = [("x", t_int), ("t", t_bool)]


@pytest.mark.parametrize("name,ty", vars_to_test)
def test_core_var(name, ty):
    type_info = extract_all_types([ty])
    node = create_var_node(name, ty, type_info[ty])
    assert node().get_core() == Var(name)
