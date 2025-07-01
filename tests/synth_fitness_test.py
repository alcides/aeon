from __future__ import annotations

import pytest

from aeon.logger.logger import setup_logger
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer

from tests.driver import check_and_return_core

setup_logger()


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
    mapping = synthesize_holes(
        ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer=GESynthesizer(), budget=0.25
    )

    assert len(mapping) == 1


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

    synthesizer = GESynthesizer()

    mapping = synthesize_holes(ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer, budget=0.25)
    assert len(mapping) > 0
