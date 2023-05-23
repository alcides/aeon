from __future__ import annotations

from abc import ABC

from aeon.core.types import top
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.synthesis_grammar.grammar import mk_method_core_literal
from aeon.synthesis_grammar.grammar import Synthesizer
from aeon.typechecking.typeinfer import check_type_errors


def mock_literal_individual(value: int):
    class t_Int(ABC):
        pass

    class literal_Int(t_Int):
        value: int

        def __init__(self, value: int):
            self.value = value

    literal_Int = mk_method_core_literal(literal_Int)

    return literal_Int(value)


def test_fitness():
    code = """
        def fitness (i : Int) : Int { 2023 - i}
        def synth_int : Int = (?hole: Int) * 7;
    """
    prog: Program = parse_program(code)
    p, ctx, ectx = desugar(prog)
    check_type_errors(ctx, p, top)
    synthesizer = Synthesizer(ctx, p, top, ectx)

    individual1 = mock_literal_individual(value=4)
    individual2 = mock_literal_individual(value=289)

    expected_output1 = 1995
    expected_output2 = 0

    assert synthesizer.fitness(individual1) == expected_output1
    assert synthesizer.fitness(individual2) == expected_output2
