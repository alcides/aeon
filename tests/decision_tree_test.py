from __future__ import annotations

from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer

from tests.driver import check_and_return_core


def test_decision_tree_simple_constant():
    """Decision tree should synthesize a constant for constant data."""
    source = r"""
        @csv_data("1.0,5.0\n2.0,5.0\n3.0,5.0")
        def f(x:Float) : Float := ?hole
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
        def f(x:Float) : Float := ?hole
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
        def f(a:Float) (b:Float) : Float := ?hole
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


def test_decision_tree_single_example_int():
    """A single @example decorator provides enough training data."""
    source = """
        @example(f 2 = 3)
        def f (x : Int) : Int := ?hole
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
    assert list(mapping.values())[0] is not None


def test_decision_tree_int_threshold_uses_float_split():
    """Int feature splits compare ``toFloat n <= thresh`` to match sklearn thresholds."""
    source = """
        @example(double 3 = 6)
        @example(double 4 = 8)
        def double (n : Int) : Int := ?hole
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
    term = list(mapping.values())[0]
    assert term is not None

    from aeon.core.substitutions import substitution
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.pbt import run_examples
    from aeon.synthesis.uis.api import SynthesisUI

    hole_name = incomplete_functions[0][1][0]
    core_filled = substitution(core_ast_anf, term, hole_name)
    driver = AeonDriver(AeonConfig(synthesizer="decision_tree", synthesis_ui=SynthesisUI(), synthesis_budget=5))
    driver.core = core_filled
    driver.evaluation_ctx = ectx
    driver.metadata = metadata
    results = run_examples(driver.evaluation_ctx, driver.core, driver.metadata)
    assert all(r.passed for r in results), [r.summary() for r in results]


def test_decision_tree_multiple_examples():
    """Multiple @example decorators merge into training data."""
    source = """
        @example(f 1.0 = 10.0)
        @example(f 2.0 = 10.0)
        @example(f 8.0 = 20.0)
        @example(f 9.0 = 20.0)
        def f (x : Float) : Float := ?hole
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
    assert list(mapping.values())[0] is not None


def test_decision_tree_example_with_csv_data():
    """@example and @csv_data decorators can be combined."""
    source = r"""
        @csv_data("1.0,10.0\n2.0,10.0")
        @example(f 8.0 = 20.0)
        @example(f 9.0 = 20.0)
        def f (x : Float) : Float := ?hole
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
    assert list(mapping.values())[0] is not None
