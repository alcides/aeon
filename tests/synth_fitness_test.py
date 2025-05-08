from __future__ import annotations

import pytest

from aeon.core.terms import Term, Literal
from aeon.core.types import t_int
from aeon.logger.logger import setup_logger
from aeon.synthesis_grammar.identification import incomplete_functions_and_holes
from aeon.synthesis_grammar.synthesizer import synthesize, gengy_default_config

from tests.driver import check_and_return_core

setup_logger()

synth_config = gengy_default_config
synth_config["timer_limit"] = 0.25


def test_fitness():
    source = """def year : Int = 2023;
            @minimize_int( year - synth(7) )
            def synth (i:Int) : Int {(?hole: Int) * i}
        """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(
        ctx,
        core_ast_anf,
    )
    term, _ = synthesize(ctx, ectx, core_ast_anf, incomplete_functions, metadata, synth_config=synth_config)

    assert isinstance(term, Term)


@pytest.mark.skip(reason="Synthesis-only")
def test_literal_int_range():
    source = """
            @minimize_int(1)
            def synth : Int = ?hole;
        """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(
        ctx,
        core_ast_anf,
    )
    term, _ = synthesize(ctx, ectx, core_ast_anf, incomplete_functions, metadata, synth_config=synth_config)

    assert isinstance(term, Term)
    assert isinstance(term, Literal)
    assert term.type == t_int
    assert -1 <= term.value <= 256
