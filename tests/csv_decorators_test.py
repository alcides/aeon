from __future__ import annotations

import os
import tempfile

import pytest

from aeon.logger.logger import setup_logger
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer

from tests.driver import check_and_return_core

setup_logger()


def test_csv_data_decorator_parses():
    """Test that @csv_data generates a valid fitness function."""
    source = r"""
        @csv_data("1.0,2.0,3.0\n4.0,5.0,9.0")
        def f(a:Float) (b:Float) : Float { ?hole }
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
    assert len(incomplete_functions) == 1


def test_csv_file_decorator_parses():
    """Test that @csv_file generates a valid fitness function."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".csv", delete=False) as f:
        f.write("1.0,2.0,3.0\n4.0,5.0,9.0\n")
        tmpfile = f.name

    try:
        source = f"""
            @csv_file("{tmpfile}")
            def f(a:Float) (b:Float) : Float {{ ?hole }}
        """
        core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
        incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
        assert len(incomplete_functions) == 1
    finally:
        os.unlink(tmpfile)


def test_csv_data_metadata_has_goals():
    """Test that csv_data populates metadata with goals."""
    source = r"""
        @csv_data("1.0,2.0\n3.0,4.0")
        def f(x:Float) : Float { ?hole }
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    # Metadata should have goals for the function
    assert any("goals" in v for v in metadata.values() if isinstance(v, dict))


@pytest.mark.skip(reason="Synthesis-only")
def test_csv_data_synthesis():
    """Test that synthesis works with csv_data decorator."""
    source = r"""
        @csv_data("1.0,2.0\n2.0,4.0\n3.0,6.0")
        def f(x:Float) : Float { ?hole }
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
    mapping = synthesize_holes(
        ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer=GESynthesizer(), budget=0.5
    )
    assert len(mapping) > 0
