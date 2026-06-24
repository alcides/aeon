"""Functional coverage for the (1+1)-ES (``1p1``) and hill-climbing (``hc``)
search strategies.

Both reuse ``GESynthesizer`` -- the engine that ``gp``/``enumerative``/
``random_search`` already exercise end-to-end -- so the rest of the suite only
smoke-constructs them (``synthesizer_seed_test``). These confirm the factory
wires each strategy and that each actually synthesizes a well-typed term for a
basic-typed hole.
"""

from __future__ import annotations

import pytest

from aeon.core.terms import Term
from aeon.core.types import top, t_bool, t_int
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.typechecking.typeinfer import check_type

from tests.driver import check_and_return_core

STRATEGIES = [("1p1", "one_plus_one"), ("hc", "hill_climbing")]
TYPES = [("Int", t_int), ("Bool", t_bool)]


def _synthesize(code: str, method: str, budget: float = 2.0):
    term, ctx, ectx, metadata = check_and_return_core(code)
    assert check_type(ctx, term, top)
    targets = incomplete_functions_and_holes(ctx, term)
    holes = synthesize_holes(ctx, ectx, term, targets, metadata, GESynthesizer(method=method), budget=budget)
    return holes[next(iter(holes))], ctx


@pytest.mark.parametrize("backend_id,method", STRATEGIES)
def test_factory_registers_strategy(backend_id, method):
    synth = make_synthesizer(backend_id)
    assert isinstance(synth, GESynthesizer)
    assert synth.method == method


@pytest.mark.parametrize("backend_id,method", STRATEGIES)
@pytest.mark.parametrize("type_name,ty", TYPES)
def test_synthesizes_basic_typed_hole(backend_id, method, type_name, ty):
    t, ctx = _synthesize(f"def s : {type_name} := ?hole;", method)
    assert isinstance(t, Term)
    assert check_type(ctx, t, ty)
