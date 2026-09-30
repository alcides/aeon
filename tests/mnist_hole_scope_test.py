"""MNIST Arch hole should offer constructors (and if), not Array/ops/projectors."""

from __future__ import annotations

from collections import Counter

from aeon.core.terms import Application, If, RefinementApplication, TypeApplication, Var
from aeon.core.types import top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.native_search import expansions_for_hole, initial_partial, make_skip
from aeon.synthesis.modules.tdsyn.helpers import clear_tdsyn_caches
from aeon.synthesis.scope import shadow_fitness_helpers, without_excluded_names
from aeon.synthesis.uis.api import SilentSynthesisUI

MNIST = "examples/synthesis/neuroevolution/mnist.ae"


def _expansion_heads(filename: str) -> Counter[str]:
    clear_tdsyn_caches()
    cfg = AeonConfig(synthesizer="random_search", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    list(driver.parse(filename=filename))
    core, ctx, metadata = driver.core, driver.typing_ctx, driver.metadata
    targets = incomplete_functions_and_holes(ctx, core)
    assert targets, "expected a synthesis hole"
    fun_name, holes = targets[0]
    program_holes = get_holes_info(ctx, core, top, targets, refined_types=True)
    _ty, tyctx = program_holes[holes[0]]
    tyctx = without_excluded_names(shadow_fitness_helpers(tyctx, metadata))
    skip = make_skip(fun_name, metadata)
    initial = initial_partial(tyctx, _ty)
    counts: Counter[str] = Counter()
    for partial in expansions_for_hole(initial, initial.holes[0], skip, max_depth=None):
        term = partial.term
        if isinstance(term, If):
            counts["if"] += 1
            continue
        head = term
        while isinstance(head, (Application, TypeApplication, RefinementApplication)):
            head = head.fun if isinstance(head, Application) else head.body
        if isinstance(head, Var):
            counts[head.name.name] += 1
        else:
            counts[type(head).__name__] += 1
    return counts


def test_mnist_arch_hole_is_constructor_grammar():
    counts = _expansion_heads(MNIST)
    heads = set(counts)
    assert heads <= {
        "Arch_arch_out",
        "Arch_arch_relu16",
        "Arch_arch_relu32",
        "Arch_arch_relu64",
        "Arch_arch_tanh16",
        "Arch_arch_tanh32",
        "Arch_arch_sigmoid16",
        "Arch_arch_sigmoid32",
        "if",
    }, heads
    assert "Arch_arch_out" in heads
    assert not any(h.endswith("_rest") or h == "Arch_rec" for h in heads)
    assert not any(h.startswith("Array_") or h in {"+", "-", "*", "/", "$", "__index__"} for h in heads)
