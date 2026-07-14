"""Unit tests for the GenomicNG (Nevergrad grammatical-evolution) synthesizer."""

from __future__ import annotations

import pytest

from aeon.core.terms import Term
from aeon.logger.logger import setup_logger
from aeon.synthesis.grammar.genomic_ng import (
    GenomicNGSynthesizer,
    _knee_point,
    _orient,
)
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer

from tests.driver import check_and_return_core
from tests.synthesis_helpers import first_hole_term, synthesize_holes_or_skip

setup_logger()

pytest.importorskip("nevergrad")


# ---------------------------------------------------------------------------
# _orient: re-orient fitness so every objective is minimised
# ---------------------------------------------------------------------------


def test_orient_minimize_unchanged():
    assert _orient([3.0, -2.0], [True, True]) == [3.0, -2.0]


def test_orient_maximize_negated():
    assert _orient([3.0, -2.0], [False, False]) == [-3.0, 2.0]


def test_orient_mixed():
    assert _orient([3.0, 5.0], [True, False]) == [3.0, -5.0]


# ---------------------------------------------------------------------------
# _knee_point: compromise selection over an oriented-loss archive
# ---------------------------------------------------------------------------


def test_knee_point_empty_returns_none():
    assert _knee_point([], [True]) is None


def test_knee_point_single_returns_only():
    term = object()
    assert _knee_point([(term, [4.0])], [True]) is term


def test_knee_point_single_objective_picks_lowest():
    lo, hi = object(), object()
    chosen = _knee_point([(hi, [9.0]), (lo, [1.0])], [True])
    assert chosen is lo


def test_knee_point_prefers_balanced_compromise():
    # Two extreme points and one balanced one; the balanced candidate is the
    # closest to the (normalised) utopia origin and should win.
    a = object()  # extreme on objective 0
    b = object()  # extreme on objective 1
    knee = object()  # compromise
    archive = [(a, [0.0, 10.0]), (b, [10.0, 0.0]), (knee, [2.0, 2.0])]
    assert _knee_point(archive, [True, True]) is knee


# ---------------------------------------------------------------------------
# Factory routing
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "name,optimizer",
    [
        ("ng", "NGOpt"),
        ("genomic_ng", "NGOpt"),
        ("ng_cma", "CMA"),
        ("ng_de", "DE"),
        ("ng_pso", "PSO"),
    ],
)
def test_factory_routes_to_genomic_ng(name, optimizer):
    syn = make_synthesizer(name)
    assert isinstance(syn, GenomicNGSynthesizer)
    assert syn.optimizer == optimizer


# ---------------------------------------------------------------------------
# End-to-end synthesis
# ---------------------------------------------------------------------------


def test_single_objective_synthesis_fills_hole():
    source = """def year : Int := 2023;
            @minimize_int( year - synth 7 )
            def synth (i:Int) : Int := (?hole: Int) * i
        """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
    mapping = synthesize_holes_or_skip(
        ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer=GenomicNGSynthesizer(), budget=2.0
    )
    assert len(mapping) == 1
    term = first_hole_term(mapping)
    assert isinstance(term, Term)


def test_multi_objective_synthesis_fills_hole():
    # Two objectives and an unrefined return type: every well-typed candidate is
    # valid, so the multi-objective knee-point selection path is exercised
    # reliably (independent of search luck on a rare refinement).
    source = """
            def soft_a (n: Int) : Int := (n * n) - 5
            def soft_b (n: Int) : Int := n + 4
            @minimize_int(soft_a (func 10))
            @minimize_int(soft_b (func 21))
            def func (i:Int) : Int := ?hole
        """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
    mapping = synthesize_holes_or_skip(
        ctx, ectx, core_ast_anf, incomplete_functions, metadata, synthesizer=GenomicNGSynthesizer(), budget=3.0
    )
    assert len(mapping) == 1
    term = first_hole_term(mapping)
    assert isinstance(term, Term)


def test_alternative_optimizer_runs():
    source = """def year : Int := 2023;
            @minimize_int( year - synth 7 )
            def synth (i:Int) : Int := (?hole: Int) * i
        """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete_functions = incomplete_functions_and_holes(ctx, core_ast_anf)
    mapping = synthesize_holes_or_skip(
        ctx,
        ectx,
        core_ast_anf,
        incomplete_functions,
        metadata,
        synthesizer=GenomicNGSynthesizer(optimizer="CMA"),
        budget=2.0,
    )
    assert len(mapping) == 1
    first_hole_term(mapping)
