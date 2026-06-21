"""Regression tests for ``flatten``'s binder alpha-renaming.

``flatten`` renames every ``forall`` binder to a globally fresh name. The
implementation defers the renamings and applies them in a single pass (instead
of eagerly rebuilding the remaining constraint at each binder, which was
O(depth^2)); these tests pin the observable invariants that refactor must keep:
consistent renaming across premise/conclusion, distinct fresh names per binder,
and no leakage of a binder into a sibling scope.

``fresh_counter`` is pinned to a high base in each test so the fresh ids can't
coincide with the small original binder ids used here.
"""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar, liquid_free_vars
from aeon.core.types import t_int
from aeon.utils.name import Name, fresh_counter
from aeon.verification.smt import flatten
from aeon.verification.vcs import Conjunction, Implication, LiquidConstraint


def _gt(a, b):
    return LiquidApp(Name(">", 0), [a, b])


def _ids(term, name: str) -> list[int]:
    return [n.id for n in liquid_free_vars(term) if n.name == name]


def test_binder_is_renamed_consistently_in_premise_and_conclusion():
    fresh_counter.counter = 1000
    x = Name("x", 1)  # id 1 -- fresh ids will be >= 1001, so no coincidence
    c = Implication(
        x, t_int, _gt(LiquidVar(x), LiquidLiteralInt(0)), LiquidConstraint(_gt(LiquidVar(x), LiquidLiteralInt(0)))
    )
    [cc] = list(flatten(c))
    prem, conc = _ids(cc.premise, "x"), _ids(cc.conclusion, "x")
    assert prem and conc
    assert all(i != 1 for i in prem + conc), "binder must be renamed off its original id"
    assert set(prem) == set(conc), "premise and conclusion must share the fresh name"


def test_nested_binders_get_distinct_fresh_names():
    fresh_counter.counter = 1000
    x, y = Name("x", 1), Name("y", 2)
    inner = Implication(y, t_int, _gt(LiquidVar(y), LiquidVar(x)), LiquidConstraint(_gt(LiquidVar(y), LiquidVar(x))))
    outer = Implication(x, t_int, _gt(LiquidVar(x), LiquidLiteralInt(0)), inner)
    [cc] = list(flatten(outer))
    xi, yi = _ids(cc.conclusion, "x")[0], _ids(cc.conclusion, "y")[0]
    assert xi != 1 and yi != 2  # both renamed
    assert xi != yi  # to distinct fresh ids


def test_sibling_scopes_do_not_leak():
    # (forall x:Int, x>0) ∧ (forall x:Int, x>0) -- same original binder in two
    # arms; each must get its OWN fresh id (verifies the deferred-rename restore).
    fresh_counter.counter = 1000

    def arm():
        x = Name("x", 1)
        return Implication(
            x, t_int, _gt(LiquidVar(x), LiquidLiteralInt(0)), LiquidConstraint(_gt(LiquidVar(x), LiquidLiteralInt(0)))
        )

    ccs = list(flatten(Conjunction(arm(), arm())))
    assert len(ccs) == 2
    id0, id1 = _ids(ccs[0].conclusion, "x")[0], _ids(ccs[1].conclusion, "x")[0]
    assert id0 != 1 and id1 != 1 and id0 != id1, "each sibling binder must be independently fresh"


def test_flatten_is_deterministic_given_fresh_counter():
    x = Name("x", 1)
    c = Implication(
        x, t_int, _gt(LiquidVar(x), LiquidLiteralInt(0)), LiquidConstraint(_gt(LiquidVar(x), LiquidLiteralInt(0)))
    )
    fresh_counter.counter = 5000
    a = list(flatten(c))
    fresh_counter.counter = 5000
    b = list(flatten(c))
    assert len(a) == len(b) == 1
    assert a[0].conclusion == b[0].conclusion and a[0].premise == b[0].premise
