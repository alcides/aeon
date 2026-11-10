"""Complete-program checks reuse successful fitness without repeating execution."""

import pytest

from aeon.core.substitutions import substitution
from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis import fitness_eval
from aeon.synthesis.api import InvalidIndividualException
from aeon.synthesis.evaluation_pool import _CTX
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.program_specifications import ProgramSpecifications
from tests.joint_hole_synthesis_test import parse


def specifications(source, **kwargs):
    driver = parse(source)
    return ProgramSpecifications(
        driver.typing_ctx,
        driver.evaluation_ctx,
        driver.core,
        incomplete_functions_and_holes(driver.typing_ctx, driver.core),
        driver.metadata,
        **kwargs,
    )


def test_pooled_checks_reuse_fitness_vector_and_refresh_for_each_candidate(monkeypatch):
    calls = _CTX.Value("i", 0)
    collect = fitness_eval._collect_expression_goals

    def counted(*args, **kwargs):
        with calls.get_lock():
            calls.value += 1
        return collect(*args, **kwargs)

    monkeypatch.setattr(fitness_eval, "_collect_expression_goals", counted)
    with specifications("""
        import Array;
        @multi_minimize_int(native "[7, 8]", 2)
        @example(f = 2)
        @maximize_int(f)
        def f : {v:Int | 1 <= v && v <= 2} := ?h;
    """) as specs:
        hole = specs.holes[0]
        assert not specs.validate(specs.candidate({hole: Literal(1, t_int)}))
        assert calls.value == 1
        good = specs.candidate({hole: Literal(2, t_int)})
        assert specs.validate(good)
        assert specs.evaluate(good) == [7.0, 8.0, 0.0, 2.0]
        assert calls.value == 2


def test_omitted_objective_still_enforces_hard_constraint():
    with specifications(
        """
        @example(f = 2)
        @maximize_int(f)
        def f : {v:Int | 1 <= v && v <= 2} := ?h;
    """,
        omit_objectives=frozenset({"example"}),
    ) as specs:
        hole = specs.holes[0]
        assert not specs.validate(specs.candidate({hole: Literal(1, t_int)}))
        good = specs.candidate({hole: Literal(2, t_int)})
        assert specs.validate(good)
        assert specs.evaluate(good) == [2.0]


def test_failed_fitness_does_not_hide_independent_constraint_result(monkeypatch):
    def failed_measure(thunk):
        raise RuntimeError("unavailable meter")

    monkeypatch.setattr(fitness_eval, "measure_cputime", failed_measure)
    with specifications("""
        @example(f = 2)
        @minimize_cputime(f)
        def f : {v:Int | 1 <= v && v <= 2} := ?h;
    """) as specs:
        hole = specs.holes[0]
        assert not specs.validate(specs.candidate({hole: Literal(1, t_int)}))
        good = specs.candidate({hole: Literal(2, t_int)})
        assert specs.validate(good)
        with pytest.raises(InvalidIndividualException):
            specs.evaluate(good)


def test_bulk_replacement_preserves_linear_binders_and_fills_every_hole():
    with specifications(
        """
        def first : Int := let 1 x : Int := ?a in x;
        def second : Int := let 1 y : Int := ?b in y;
    """,
        pooled=False,
    ) as specs:
        mapping = {hole: Literal(index, t_int) for index, hole in enumerate(specs.holes, 1)}
        expected = specs.program
        for hole, value in mapping.items():
            expected = substitution(expected, value, hole)
        candidate = specs.candidate(mapping)
        assert specs.replace(candidate) == expected
        assert specs.validate(candidate)
