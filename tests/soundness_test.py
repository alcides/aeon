from __future__ import annotations

import random

import pytest

from aeon.core.liquid import LiquidTerm
from aeon.core.terms import Term
from aeon.core.types import BaseType
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import Type
from aeon.synthesis.choice_manager import ChoiceManager
from aeon.synthesis.choice_manager import GrammaticalEvolutionManager
from aeon.synthesis.sources import ListRandomSource
from aeon.synthesis.sources import SeededRandomSource
from aeon.synthesis.term_synthesis import NoMoreBudget
from aeon.synthesis.term_synthesis import synth_term
from aeon.synthesis.type_synthesis import synth_liquid
from aeon.synthesis.type_synthesis import synth_type
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.liquid import type_infer_liquid
from aeon.typechecking.typeinfer import check_type
from aeon.typechecking.well_formed import inhabited
from aeon.typechecking.well_formed import wellformed


def listr(x):
    return ListRandomSource(x)


def rseed():
    return listr([random.randint(-100000, 100000) for _ in range(10000)])


def random_base_type() -> BaseType:
    return random.choice([t_bool, t_int])


def random_base_context() -> TypingContext:
    size = random.randint(0, 10)
    ctx: TypingContext = EmptyContext()
    for i in range(size):
        ctx = VariableBinder(ctx, f"v{i}", random_base_type())
    return ctx


@pytest.mark.parametrize("target_ty", [t_bool, t_int])
@pytest.mark.parametrize("seed", range(10))
def test_soundness_fixed(target_ty, seed) -> None:
    man = GrammaticalEvolutionManager()
    ctx = EmptyContext().with_var("a", t_int).with_var("b", t_bool)
    s: LiquidTerm = synth_liquid(man, SeededRandomSource(seed), ctx, target_ty)
    gen = type_infer_liquid(ctx, s)
    assert gen is None or gen == target_ty


def test_soundness_liq() -> None:
    man = GrammaticalEvolutionManager()
    for _ in range(1000):  # TODO add support for hypothesis.
        target_ty = random_base_type()
        ctx = random_base_context()
        try:
            s: LiquidTerm = synth_liquid(
                man,
                rseed(),
                ctx,
                target_ty,
            )
            gen = type_infer_liquid(ctx, s)
            assert gen == target_ty
        except NoMoreBudget:
            pass


def test_soundess_types() -> None:
    for _ in range(10):
        man: ChoiceManager = GrammaticalEvolutionManager()
        ctx = random_base_context()
        t: Type = synth_type(man, rseed(), ctx, d=2)
        assert wellformed(ctx, t)


def test_soundess_terms() -> None:
    for _ in range(10):
        man: ChoiceManager = GrammaticalEvolutionManager()
        ctx = random_base_context()
        ty: Type = synth_type(man, rseed(), ctx, d=2)
        assert wellformed(ctx, ty)
        if inhabited(ctx, ty):
            continue
        try:
            t: Term = synth_term(man, rseed(), ctx, ty)
            assert t is not None
            assert check_type(ctx, t, ty)
        except NoMoreBudget:
            pass
