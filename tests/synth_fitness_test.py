from __future__ import annotations

import pytest

from aeon.core.terms import Term, Literal
from aeon.core.types import t_int
from aeon.logger.logger import setup_logger
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize
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
    term, _ = synthesize(ctx, ectx, core_ast_anf, incomplete_functions, metadata, budget=0.25)

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

    synthesizer = GESynthesizer()

    term, _ = synthesize(ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer, budget=0.25)

    assert isinstance(term, Term)
    assert isinstance(term, Literal)
    assert term.type == t_int
    assert -1 <= term.value <= 256
