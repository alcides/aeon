from __future__ import annotations

from abc import ABC

from aeon.core.terms import Term
from aeon.logger.logger import setup_logger
from aeon.sugar.program import Definition, SApplication, SLiteral, SVar
from aeon.sugar.stypes import SBaseType
from aeon.synthesis_grammar.grammar import mk_method_core_literal
from aeon.synthesis_grammar.synthesizer import synthesize

from tests.driver import check_and_return_core

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
    source = """def year : Int = 2023;
        def synth (i: Int): Int { (?hole: Int) * i}
    """

    core_ast_anf, ctx, ectx, _ = check_and_return_core(source)

    internal_minimize = Definition(
        name="__internal__minimize_int_synth_0",
        foralls=[],
        args=[],
        type=SBaseType("Int"),
        body=SApplication(
            SApplication(SVar("synth"), SLiteral(7, SBaseType("Int"))),
            SApplication(SVar("-"), SVar("synth")),
        ),
    )
    term, _ = synthesize(
        ctx,
        ectx,
        core_ast_anf,
        [("synth", ["hole"])],
        {
            "synth": {
                "minimize_int": [internal_minimize],
            },
        },
    )

    assert isinstance(term, Term)


def test_fitness2():
    source = """def year : Int = 2023;
            @minimize_int( year - synth(7) )
            def synth (i:Int) : Int {(?hole: Int) * i}
        """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    term, _ = synthesize(ctx, ectx, core_ast_anf, [("synth", ["hole"])],
                         metadata)

    assert isinstance(term, Term)
