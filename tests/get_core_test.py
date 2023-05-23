from __future__ import annotations

from abc import ABC

from aeon.core.terms import Application
from aeon.core.terms import Literal
from aeon.core.terms import Var
from aeon.core.types import t_int
from aeon.synthesis_grammar.grammar import mk_method_core
from aeon.synthesis_grammar.grammar import mk_method_core_literal


class t_Int(ABC):
    pass


class literal_Int(t_Int):
    value: int

    def __init__(self, value: int):
        self.value = value


class app_f(t_Int):
    i: t_Int

    def __init__(self, i: t_Int):
        self.i = i


literal_Int = mk_method_core_literal(literal_Int)
app_f = mk_method_core(app_f)


def test_get_core():
    assert literal_Int(5).get_core() == Literal(5, t_int)
    assert app_f(literal_Int(10)).get_core() == Application(Var("f"), Literal(10, t_int))
