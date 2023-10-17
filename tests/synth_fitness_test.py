from __future__ import annotations

from abc import ABC

from aeon.core.terms import Term
from aeon.core.types import top
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.synthesis_grammar.grammar import mk_method_core_literal
from aeon.synthesis_grammar.synthesizer import synthesize
from aeon.typechecking.typeinfer import check_type_errors


def mock_literal_individual(value: int):

    class t_Int(ABC):
        pass

    class literal_Int(t_Int):
        value: int

        def __init__(self, value: int):
            self.value = value

    literal_int_instance = mk_method_core_literal(literal_Int)  # type: ignore

    return literal_int_instance(value)  # type: ignore


def test_fitness():
    code = """
        def year : Int = 2023;
        def synth : Int = (?hole: Int) * 7;
        def __internal__fitness_function_synth : Int  =  year - synth;
    """
    prog = parse_program(code)
    p, ctx, ectx = desugar(prog)
    p = ensure_anf(p)
    check_type_errors(ctx, p, top)
    term = synthesize(ctx, ectx, p, [("synth", ["hole"])])

    assert isinstance(term, Term)
