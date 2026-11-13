"""Native BFS and random walks prune QTT violations before validation."""

import random
from itertools import islice
from time import monotonic

import pytest

from aeon.core.multiplicity import M0, M1
from aeon.core.terms import Abstraction, Annotation, Application, Literal, Var
from aeon.core.types import AbstractionType, t_int
from aeon.synthesis.joint import HoleSpec
from aeon.synthesis.modules.enumerative import EnumerativeSynthesizer, iter_candidates
from aeon.synthesis.modules.random_search import RandomSearchSynthesizer, iter_random_candidates
from aeon.synthesis.modules.native_search import initial_partial, literal_completions, sample_one
from aeon.synthesis.qtt import QTTValidator
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.linearity import check_linearity
from aeon.utils.name import Name
from tests.tdsyn_relations_test import _driver


def candidates(backend, ctx, typ, check_sketch=None):
    if backend == "enumerative":
        return list(
            iter_candidates(ctx, typ, Name("target", 20), {}, max_depth=1, max_expansions=4, check_sketch=check_sketch)
        )
    return list(
        islice(
            iter_random_candidates(
                ctx,
                typ,
                Name("target", 20),
                {},
                random.Random(0),
                max_depth=2,
                deadline=monotonic() + 2,
                check_sketch=check_sketch,
            ),
            10,
        )
    )


@pytest.mark.parametrize("backend", ["enumerative", "random_search"])
@pytest.mark.parametrize("mult", [M0, M1])
def test_generated_functions_obey_original_parameter_multiplicity(backend, mult):
    ctx = TypingContext()
    typ = AbstractionType(Name("x", 1), t_int, t_int, multiplicity=mult)
    terms = candidates(backend, ctx, typ)
    assert terms
    assert all(not check_linearity(Annotation(term, typ), ctx) for term in terms)


def test_literal_completion_cannot_discard_linear_parameter():
    typ = AbstractionType(Name("x", 1), t_int, t_int, multiplicity=M1)
    initial = initial_partial(TypingContext(), typ)
    assert not literal_completions(initial)
    term = sample_one(initial, lambda _: False, random.Random(0))
    assert isinstance(term, Abstraction)
    assert term.body == Var(term.var_name)


def sketch_setup():
    x, f, a, b = Name("x", 1), Name("combine", 2), Name("a", 3), Name("b", 4)
    ctx = TypingContext().with_var(x, t_int)
    full_ctx = TypingContext().with_var(
        f,
        AbstractionType(a, t_int, AbstractionType(b, t_int, t_int, multiplicity=M1), multiplicity=M1),
    )
    typ = AbstractionType(x, t_int, t_int, multiplicity=M1)

    def sketch(left, right):
        return Annotation(Abstraction(x, Application(Application(Var(f), left), right)), typ)

    return x, ctx, full_ctx, sketch


@pytest.mark.parametrize("backend", ["enumerative", "random_search"])
def test_search_counts_uses_outside_hole(backend):
    x, ctx, full_ctx, sketch = sketch_setup()
    validator = QTTValidator(lambda _: True, lambda term: sketch(Var(x), term), full_ctx)
    terms = candidates(backend, ctx, t_int, check_sketch=validator.feasible)
    assert terms
    assert all(validator.feasible(term) for term in terms)
    assert Var(x) not in terms


def test_joint_random_search_shares_budget_between_holes():
    x, ctx, full_ctx, sketch = sketch_setup()
    validator = QTTValidator(lambda _: True, lambda product: sketch(*product.terms), full_ctx)
    holes = tuple(
        HoleSpec(Name(name, i), Name("target", 20), t_int, ctx) for i, name in enumerate(("left", "right"), 30)
    )
    result = RandomSearchSynthesizer().synthesize_joint(
        holes,
        validator,
        lambda _: [],
        Name("target", 20),
        {},
        budget=2,
        ui=SilentSynthesisUI(),
    )
    assert result is not None
    assert validator.feasible(result)
    assert isinstance(result.terms[0], Literal)
    assert result.terms[1] == Var(x)


@pytest.mark.parametrize("backend", [EnumerativeSynthesizer, RandomSearchSynthesizer])
def test_direct_synthesis_needs_no_external_qtt_validator(backend):
    ctx = TypingContext()
    typ = AbstractionType(Name("x", 1), t_int, t_int, multiplicity=M1)
    term = backend().synthesize(
        ctx, typ, lambda _: True, lambda _: [], Name("target", 20), {}, budget=2, ui=SilentSynthesisUI()
    )
    assert term is not None
    assert not check_linearity(Annotation(term, typ), ctx)


@pytest.mark.parametrize("backend", ["enumerative", "random_search"])
def test_driver_preserves_linear_parameter(backend):
    driver = _driver("def consume (1 x:Int):Int := ?body; def main (u:Int):Int := consume 7;", backend)
    driver.synth()
    assert not check_linearity(driver.core, driver.typing_ctx)


def test_failed_joint_walk_restarts_resource_allocation(monkeypatch):
    from aeon.synthesis.modules import random_search

    x, ctx, full_ctx, sketch = sketch_setup()
    validator = QTTValidator(lambda _: True, lambda product: sketch(*product.terms), full_ctx)
    holes = tuple(HoleSpec(Name(name, i), Name(name, i), t_int, ctx) for i, name in enumerate(("left", "right"), 30))
    # The first walk spends x in the left hole, then gets stuck. The next
    # complete attempt must allow x to move to the right hole instead.
    proposals = iter([Var(x), None, Literal(0, t_int), Var(x)])

    def walk(*args, check_sketch, **kwargs):
        proposal = next(proposals)
        if proposal is not None:
            assert check_sketch(proposal)
            yield proposal

    monkeypatch.setattr(random_search, "iter_random_candidates", walk)
    result = RandomSearchSynthesizer().synthesize_joint(
        holes,
        validator,
        lambda _: [],
        Name("target", 20),
        {},
        budget=2,
        ui=SilentSynthesisUI(),
    )
    assert result is not None
    assert result.terms == (Literal(0, t_int), Var(x))
