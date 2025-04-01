from __future__ import annotations

import pytest

from aeon.core.terms import Term, Literal
from aeon.core.types import BaseType
from aeon.logger.logger import setup_logger
from aeon.sugar.program import Definition
from aeon.synthesis_grammar.synthesizer import synthesize, gengy_default_config
from aeon.sugar.program import SApplication, SLiteral, SVar
from aeon.sugar.stypes import SBaseType
from aeon.utils.name import Name, fresh_counter

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
        name=Name("__internal__minimize_int_synth_0", fresh_counter.fresh()),
        foralls=[],
        args=[],
        type=SBaseType("Int"),
        body=SApplication(
            SApplication(SVar(Name("synth")), SLiteral(7, SBaseType("Int"))),
            SApplication(SVar(Name("-")), SVar(Name("synth"))),
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
    term, _ = synthesize(ctx, ectx, core_ast_anf, [("synth", ["hole"])], metadata, synth_config=synth_config)

    assert isinstance(term, Term)


@pytest.mark.skip(reason="Synthesis-only")
def test_literal_int_range():
    source = """
            @minimize_int(1)
            def synth : Int = ?hole;
        """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    term, _ = synthesize(ctx, ectx, core_ast_anf, [("synth", ["hole"])], metadata, synth_config=synth_config)

    assert isinstance(term, Term)
    assert isinstance(term, Literal)
    assert term.type == BaseType("Int")
    assert -1 <= term.value <= 256
