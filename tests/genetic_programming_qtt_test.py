"""Genome decoding shares QTT budgets across choices and joint hole replacements."""

import random
from dataclasses import replace

import pytest

from aeon.core.multiplicity import M0, M1
from aeon.core.terms import Abstraction, Annotation, Application, Literal, Var
from aeon.core.types import AbstractionType, t_int
from aeon.synthesis.joint import HoleSpec
from aeon.synthesis.modules import genetic_programming as gp
from aeon.synthesis.modules.native_search import initial_partial
from aeon.synthesis.qtt import QTTValidator
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.linearity import check_linearity
from aeon.utils.name import Name
from tests.tdsyn_relations_test import _driver


def function_goal(mult=M1):
    ctx = TypingContext()
    typ = AbstractionType(Name("x", 1), t_int, t_int, multiplicity=mult)
    return replace(initial_partial(ctx, typ), expected_type=typ, context=ctx)


@pytest.mark.parametrize("genome", [[0], [255], [4, 18, 0], [90, 12]])
def test_decoder_skips_literal_models_that_drop_linear_parameter(genome):
    initial = function_goal()
    term = gp.map_genome(genome, initial, lambda _: False)
    assert term is not None
    assert not check_linearity(Annotation(term, initial.expected_type), initial.context)


def test_erased_use_pruned_before_codon_selection(monkeypatch):
    initial = function_goal(M0)
    x = initial.term.var_name
    # Exercise grammar choices rather than the SMT literal fast path.
    monkeypatch.setattr(gp, "literal_completions", lambda _: [])
    monkeypatch.setattr(gp, "BASE_CHOICE_BUDGET", 0)
    terms = [gp.map_genome([codon], initial, lambda _: False) for codon in range(16)]
    assert any(term is not None for term in terms)
    assert all(term is None or not check_linearity(Annotation(term, initial.expected_type)) for term in terms)
    assert all(term != Abstraction(x, Var(x)) for term in terms)


def test_assessment_rejects_qtt_violation_before_fitness(monkeypatch):
    initial = function_goal()
    invalid = Abstraction(initial.term.var_name, Literal(0, t_int))
    monkeypatch.setattr(gp, "map_genome", lambda *_a, **_k: invalid)
    state = gp.GPState(random.Random(0), [True], 0.5, 0.5)
    individual = gp.Individual([0])

    def evaluate(_):
        pytest.fail("QTT-invalid individual reached fitness evaluation")

    gp._assess(
        individual, initial, lambda _: False, lambda _: True, evaluate, state, SilentSynthesisUI(), gp.monotonic(), 1
    )
    assert not individual.valid
    assert individual.fitness is None
    assert not state.pareto_front


def test_joint_decoder_shares_linear_budget_between_holes():
    x, f, a, b = Name("x", 1), Name("combine", 2), Name("a", 3), Name("b", 4)
    ctx = TypingContext().with_var(x, t_int)
    full_ctx = TypingContext().with_var(
        f,
        AbstractionType(a, t_int, AbstractionType(b, t_int, t_int, multiplicity=M1), multiplicity=M1),
    )
    signature = AbstractionType(x, t_int, t_int, multiplicity=M1)

    def sketch(candidate):
        left, right = candidate.terms
        return Annotation(Abstraction(x, Application(Application(Var(f), left), right)), signature)

    validator = QTTValidator(lambda _: True, sketch, full_ctx)
    holes = tuple(
        HoleSpec(Name(name, i), Name("target", 20), t_int, ctx) for i, name in enumerate(("left", "right"), 30)
    )
    result = gp.GeneticProgrammingSynthesizer().synthesize_joint(
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
    assert not isinstance(result.terms[1], Literal)


@pytest.mark.parametrize(
    "source",
    [
        "def identity (1 x:Int):Int := ?body; def main (u:Int):Int := identity 7;",
        "def erase (0 x:Int):Int := ?body; def main (u:Int):Int := erase 7;",
        "def identity (1 x:Int):Int := if ?cond then ?left else ?right; def main (u:Int):Int := identity 7;",
    ],
)
def test_gp_driver_returns_qtt_valid_program(source):
    driver = _driver(source, "gp", budget=5)
    driver.synth()
    assert not check_linearity(driver.core, driver.typing_ctx)
    value = driver.run()
    assert isinstance(value, int)
