import pytest

from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from tests.driver import check_and_return_core

def test_synquid():
    source = """@minimize_int(fun(25))
            def fun (i:Int) : Int  {
                let a : Int = 10*i;
                (?hole: {x:Int | x >= (-45)} ) * i - a
            }
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(
        ctx,
        core_ast_anf,
    )
    mapping = synthesize_holes(
        ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer=SynquidSynthesizer(), budget=0.25
    )
    assert len(mapping) == 1

def test_synquid_simple():
    source = """@minimize_int(1)
            def synth : Int = ?hole;
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(
        ctx,
        core_ast_anf,
    )
    mapping = synthesize_holes(
        ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer=SynquidSynthesizer(), budget=0.25
    )
    assert len(mapping) > 0     