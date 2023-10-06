from __future__ import annotations

from abc import ABC

from aeon.core.terms import Var
from aeon.core.types import top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.synthesis_grammar.grammar import mk_method_core_literal
from aeon.synthesis_grammar.synthesizer import Synthesizer
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
        def fitness : Int  =  year - synth;
    """
    prog = parse_program(code)
    p, ctx, ectx, _ = desugar(prog)
    check_type_errors(ctx, p, top)
    synthesizer = Synthesizer(ctx, p, top, ectx)

    individual1 = mock_literal_individual(value=4)
    individual2 = mock_literal_individual(value=289)

    expected_output1 = 1995
    expected_output2 = 0

    assert synthesizer.evaluate_fitness(individual1, Var("fitness"), True) == expected_output1
    assert synthesizer.evaluate_fitness(individual2, Var("fitness"), True) == expected_output2
