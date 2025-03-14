from __future__ import annotations

from aeon.core.terms import Term
from aeon.logger.logger import setup_logger
from aeon.sugar.program import Definition
from aeon.synthesis_grammar.synthesizer import synthesize, gengy_default_config
from aeon.sugar.program import SApplication, SLiteral, SVar
from aeon.sugar.stypes import SBaseType

from tests.driver import check_and_return_core

setup_logger()

synth_config = gengy_default_config
synth_config["timer_limit"] = 0.25


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
        synth_config=synth_config,
    )

    assert isinstance(term, Term)


def test_fitness2():
    source = """def year : Int = 2023;
            @minimize_int( year - synth(7) )
            def synth (i:Int) : Int {(?hole: Int) * i}
        """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    term, _ = synthesize(ctx,
                         ectx,
                         core_ast_anf, [("synth", ["hole"])],
                         metadata,
                         synth_config=synth_config)

    assert isinstance(term, Term)
