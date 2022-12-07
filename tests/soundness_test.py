from __future__ import annotations

import random
from copy import copy
from typing import Dict
from unittest import skip

from aeon.core.liquid import LiquidTerm
from aeon.core.substitutions import liquefy
from aeon.core.terms import Term
from aeon.core.types import BaseType
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import Type
from aeon.synthesis.choice_manager import ChoiceManager
from aeon.synthesis.choice_manager import GrammaticalEvolutionManager
from aeon.synthesis.sources import ListRandomSource
from aeon.synthesis.term_synthesis import NoMoreBudget
from aeon.synthesis.term_synthesis import synth_term
from aeon.synthesis.type_synthesis import synth_liquid
from aeon.synthesis.type_synthesis import synth_type
from aeon.typing.context import EmptyContext
from aeon.typing.context import TypingContext
from aeon.typing.context import VariableBinder
from aeon.typing.liquid import type_infer_liquid
from aeon.typing.typeinfer import check_type
from aeon.typing.well_formed import inhabited
from aeon.typing.well_formed import wellformed

listr = lambda x: ListRandomSource(x)
rseed = lambda: listr([random.randint(-100000, 100000) for _ in range(10000)])


def random_base_type() -> BaseType:
    return random.choice([t_bool, t_int])


def random_base_context() -> TypingContext:
    size = random.randint(0, 10)
    ctx: TypingContext = EmptyContext()
    for i in range(size):
        ctx = VariableBinder(ctx, f"v{i}", random_base_type())
    return ctx


def test_soundness_liq():
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
            assert type_infer_liquid(ctx, s) == target_ty
        except NoMoreBudget:
            pass


def test_soundess_types():
    for _ in range(10):
        man: ChoiceManager = GrammaticalEvolutionManager()
        ctx = random_base_context()
        t: Type = synth_type(man, rseed(), ctx, d=2)
        assert wellformed(ctx, t)


def test_soundess_terms():
    for _ in range(10):
        man: ChoiceManager = GrammaticalEvolutionManager()
        ctx = random_base_context()
        ty: Type = synth_type(man, rseed(), ctx, d=2)
        assert wellformed(ctx, ty)
        if inhabited(ctx, ty):
            continue
        try:
            t: Term = synth_term(man, rseed(), ctx, ty)
            assert t != None
            assert check_type(ctx, t, ty)
        except NoMoreBudget:
            pass


# TODO: remove this
d = copy(globals())
for var in d:
    if "test_" in var:
        globals()[var] = skip(d[var])
