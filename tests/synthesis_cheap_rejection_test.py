"""Do not spend the search budget proving elementary impossible lengths."""

import pytest

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.parser import parse_type
from aeon.core.terms import Literal, Var
from aeon.core.types import AbstractionType, RefinedType, TypeConstructor, t_int
from aeon.synthesis.modules.tdsyn.constraints import candidate_feasible, eager_pruning
from aeon.synthesis.modules.tdsyn.worklist import TypedHole
from aeon.typechecking.context import TypingContext, TypeConstructorBinder, UninterpretedBinder
from aeon.utils.name import Name


def app(op, *args):
    return LiquidApp(Name(op, 0), list(args))


@pytest.mark.parametrize("prune", [False, True])
def test_scalar_length_mismatch_rejected_without_smt(monkeypatch, prune):
    hole = TypedHole(Name("n", 0), parse_type("{v:Int | v == 50}"), TypingContext())
    # Instrument the query boundary, not elapsed time: this must be cheap
    # even with eager SMT pruning disabled by random search and GP.
    queries = []
    monkeypatch.setattr("aeon.synthesis.modules.tdsyn.constraints.feasible", lambda *args: queries.append(args) or True)
    token = eager_pruning.set(prune)
    try:
        assert not candidate_feasible(hole, Literal(4, t_int), [])
        assert not queries
    finally:
        eager_pruning.reset(token)


def test_length_constraint_propagates_through_an_unfinished_array_map(monkeypatch):
    array = TypeConstructor(Name("Array", 0), [t_int])
    result, child, binder = Name("result", 0), Name("child", 0), Name("v", 0)

    def size(name):
        return app("size", LiquidVar(name))

    ctx = TypingContext(
        [
            TypeConstructorBinder(Name("Array", 0), [Name("a", 0)]),
            UninterpretedBinder(Name("size", 0), AbstractionType(binder, array, t_int)),
        ]
    )
    wanted = RefinedType(binder, array, app("==", size(binder), LiquidLiteralInt(50)))
    empty = RefinedType(binder, array, app("==", size(binder), LiquidLiteralInt(0)))
    hole = TypedHole(child, array, ctx, constraints=[app("==", size(result), size(child))], bindings={result: wanted})
    token = eager_pruning.set(False)
    try:
        assert not candidate_feasible(hole, Var(Name("empty", 0)), [], actual_type=empty)
    finally:
        eager_pruning.reset(token)


@pytest.mark.parametrize("value", [50, 51])
def test_symbolic_or_compatible_constraints_remain_available(value):
    # A symbolic equality is not a contradiction; defer it to the full solver.
    n, other = Name("n", 0), Name("other", 0)
    ty = RefinedType(n, t_int, app("==", LiquidVar(n), LiquidVar(other)))
    hole = TypedHole(n, ty, TypingContext().with_var(other, t_int))
    token = eager_pruning.set(False)
    try:
        assert candidate_feasible(hole, Literal(value, t_int), [])
    finally:
        eager_pruning.reset(token)


def test_disjunctions_and_user_functions_are_not_treated_as_builtin_equalities():
    from aeon.synthesis.grammar.constant_constraints import conflicting_integer_equalities

    x = LiquidVar(Name("x", 0))
    four = app("==", x, LiquidLiteralInt(4))
    fifty = app("==", x, LiquidLiteralInt(50))
    assert conflicting_integer_equalities([app("&&", four, fifty)])
    assert not conflicting_integer_equalities([app("||", four, fifty)])
    custom = LiquidApp(Name("==", 99), [x, LiquidLiteralInt(50)])
    assert not conflicting_integer_equalities([four, custom])
