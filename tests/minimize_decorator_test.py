from __future__ import annotations

from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer

from tests.driver import check_and_return_core


def test_minimize_single_arg():
    """Multiple @minimize decorators provide training data for the decision tree."""
    source = """
        @minimize(f(1.0) - 5.0)
        @minimize(f(2.0) - 5.0)
        @minimize(f(3.0) - 5.0)
        def f(x:Float) : Float { ?hole }
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


def test_minimize_two_args():
    """@minimize works with multi-argument functions."""
    source = """
        @minimize(f(1.0)(0.0) - 1.0)
        @minimize(f(0.0)(1.0) - 1.0)
        @minimize(f(0.0)(0.0) - 0.0)
        @minimize(f(1.0)(1.0) - 2.0)
        def f(a:Float) (b:Float) : Float { ?hole }
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


def test_maximize_extracts_training_data():
    """@maximize also extracts training data and creates a fitness goal."""
    source = """
        @maximize(f(1.0) - 5.0)
        @maximize(f(2.0) - 5.0)
        @maximize(f(3.0) - 5.0)
        def f(x:Float) : Float { ?hole }
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


def test_minimize_combined_with_csv_data():
    """@minimize and @csv_data can be combined, merging training data."""
    source = r"""
        @csv_data("1.0,5.0\n2.0,5.0")
        @minimize(f(3.0) - 5.0)
        def f(x:Float) : Float { ?hole }
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


def test_minimize_metadata_has_training_data():
    """@minimize stores training data points in metadata."""
    source = """
        @minimize(f(1.0) - 10.0)
        @minimize(f(2.0) - 20.0)
        def f(x:Float) : Float { ?hole }
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    # Check training data exists in metadata
    training_data = None
    for key, val in metadata.items():
        if isinstance(val, dict) and "training_data" in val:
            training_data = val["training_data"]
            break
    assert training_data is not None
    assert len(training_data) == 2
    assert training_data[0] == [1.0, 10.0]
    assert training_data[1] == [2.0, 20.0]


def test_minimize_metadata_has_goals():
    """@minimize also creates fitness goals for standard synthesizers."""
    source = """
        @minimize(f(1.0) - 10.0)
        def f(x:Float) : Float { ?hole }
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    assert any("goals" in v for v in metadata.values() if isinstance(v, dict))
