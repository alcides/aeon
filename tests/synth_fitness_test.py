from __future__ import annotations

from abc import ABC

from aeon.core.terms import Term, Application, Literal, Var
from aeon.core.types import top, BaseType

from aeon.logger.logger import setup_logger
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Definition
from aeon.synthesis_grammar.grammar import mk_method_core_literal
from aeon.synthesis_grammar.synthesizer import synthesize
from aeon.typechecking.typeinfer import check_type_errors

setup_logger()


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
    code = """def year : Int = 2023;
        def synth (i: Int): Int { (?hole: Int) * i}
    """
    prog = parse_program(code)
    p, ctx, ectx, _ = desugar(prog)
    check_type_errors(ctx, p, top)
    internal_minimize = Definition(
        name="__internal__minimize_int_synth_0",
        args=[],
        type=BaseType("Int"),
        body=Application(Application(Var("synth"), Literal(7, BaseType("Int"))), Application(Var("-"), Var("synth"))),
    )
    term = synthesize(ctx, ectx, p, [("synth", ["hole"])], {"synth": {"minimize_int": [internal_minimize]}})

    assert isinstance(term, Term)


def test_fitness2():
    code = """def year : Int = 2023;
            @minimize_int( year - synth(7) )
            def synth (i:Int) : Int {(?hole: Int) * i}
        """
    prog = parse_program(code)
    p, ctx, ectx, _ = desugar(prog)
    check_type_errors(ctx, p, top)
    term = synthesize(ctx, ectx, p, [("synth", ["hole"])], metadata)

    assert isinstance(term, Term)
