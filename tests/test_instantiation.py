from aeon.core.instantiation import type_substition
from aeon.core.types import t_int, t_bool
from aeon.frontend.parser import parse_type


def test_substitution_type_simple():
    t = parse_type("a")
    assert type_substition(t, "a", t_int) == t_int


def test_substitution_type_no_change():
    assert type_substition(t_int, "a", t_bool) == t_int


# TODO: write tests
