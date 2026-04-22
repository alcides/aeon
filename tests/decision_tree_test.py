from __future__ import annotations

from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer

from tests.driver import check_and_return_core


def test_decision_tree_simple_constant():
    """Decision tree should synthesize a constant for constant data."""
    source = r"""
        @csv_data("1.0,5.0\n2.0,5.0\n3.0,5.0")
        def f(x:Float) : Float = ?hole
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
    mapping = synthesize_holes(
        ctx,
        ectx,
        core_ast_anf,
        incomplete_functions,
        metadata,
        synthesizer=DecisionTreeSynthesizer(),
        budget=5,
    )
    assert len(mapping) == 1
    result = list(mapping.values())[0]
    assert result is not None


def test_decision_tree_step_function():
    """Decision tree should learn a step function (if x <= 5 then 0 else 1)."""
    source = r"""
        @csv_data("1.0,0.0\n2.0,0.0\n3.0,0.0\n7.0,1.0\n8.0,1.0\n9.0,1.0")
        def f(x:Float) : Float = ?hole
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
    mapping = synthesize_holes(
        ctx,
        ectx,
        core_ast_anf,
        incomplete_functions,
        metadata,
        synthesizer=DecisionTreeSynthesizer(),
        budget=5,
    )
    assert len(mapping) == 1
    result = list(mapping.values())[0]
    assert result is not None


def test_decision_tree_two_args():
    """Decision tree should handle two arguments."""
    source = r"""
        @csv_data("1.0,0.0,1.0\n0.0,1.0,1.0\n0.0,0.0,0.0\n1.0,1.0,2.0")
        def f(a:Float) (b:Float) : Float = ?hole
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
    mapping = synthesize_holes(
        ctx,
        ectx,
        core_ast_anf,
        incomplete_functions,
        metadata,
        synthesizer=DecisionTreeSynthesizer(),
        budget=5,
    )
    assert len(mapping) == 1
    result = list(mapping.values())[0]
    assert result is not None
