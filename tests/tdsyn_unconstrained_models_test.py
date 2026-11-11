"""Runtime requirements must be able to reject one SMT model and try another."""

from z3 import Bool, Int, Solver

from aeon.core.types import t_bool, t_int
from aeon.synthesis.modules.tdsyn.smt_solve import _literal_models
from aeon.synthesis.modules.tdsyn.worklist import TypedHole
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def test_completion_enumerates_unconstrained_boolean_payload():
    # Array.mk_repeat's result length fixes n=50 but says nothing about b.
    # A runtime @require can reject the all-true array (weight 554 > 100).
    length, payload = Name("length", 0), Name("payload", 0)
    holes = [TypedHole(length, t_int, TypingContext()), TypedHole(payload, t_bool, TypingContext())]
    variables = {str(length): Int(str(length)), str(payload): Bool(str(payload))}
    solver = Solver()
    solver.add(variables[str(length)] == 50)
    models = _literal_models(solver, [], holes, variables, max_models=5)
    assert {(m[length].value, m[payload].value) for m in models} == {(50, False), (50, True)}
    assert any(not m[payload].value for m in models)


def test_completion_keeps_constrained_boolean_and_bounds_free_integers():
    payload, integer = Name("payload", 0), Name("integer", 0)
    holes = [TypedHole(payload, t_bool, TypingContext()), TypedHole(integer, t_int, TypingContext())]
    variables = {str(payload): Bool(str(payload)), str(integer): Int(str(integer))}
    solver = Solver()
    solver.add(variables[str(payload)])
    models = _literal_models(solver, [], holes, variables, max_models=3)
    assert len(models) == 3
    assert all(m[payload].value is True for m in models)
    assert len({m[integer].value for m in models}) == 3
