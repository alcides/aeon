from __future__ import annotations

from aeon.core.instantiation import type_substitution
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.frontend.parser import parse_type
from aeon.utils.name import Name


def test_substitution_type_simple():
    t = parse_type("a")
    assert type_substitution(t, Name("a"), t_int) == t_int


def test_substitution_type_no_change():
    assert type_substitution(t_int, Name("a"), t_bool) == t_int


# TODO: write tests
