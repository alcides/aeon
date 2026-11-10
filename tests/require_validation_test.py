"""@require rejects invalid candidates without adding objective dimensions."""

import pytest
from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.synthesis_specifications_test import solve
from tests.joint_hole_synthesis_test import parse

BACKENDS = ["gp", "random_search", "tdsyn_backward", "tdsyn_enumerative", "tdsyn_random", "synquid", "ortools"]


@pytest.fixture(params=BACKENDS)
def backend(request):
    if request.param == "ortools":
        pytest.importorskip("ortools")
    return request.param


@pytest.mark.parametrize("external", [False, True])
def test_require_rejects_false_candidates(backend, external):
    declaration = "def f : {v:Int | 0 <= v && v <= 1} := ?h;"
    source = (declaration + "@require(f = 1) def score : Int := f;") if external else "@require(f = 1) " + declaration
    result = solve(source, make_synthesizer(backend), budget=2)
    assert list(result.values()) == [Literal(1, t_int)]


def test_false_requirement_has_no_solution(backend):
    try:
        result = solve("@require(false) def f : {v:Int | v = 0} := ?h;", make_synthesizer(backend), budget=1)
    except SynthesisNotSuccessful:
        return
    assert list(result.values()) == [None]


def test_require_has_no_objective_dimensions():
    driver = parse("@require(true) def f : Int := ?h;")
    goals = [g for entry in driver.metadata.values() for g in entry.get("goals", [])]
    assert len(goals) == 1
    assert goals[0].minimize is True
    assert goals[0].kind == "require"
    assert goals[0].length == 0


def test_requirement_cannot_trade_off_against_another_objective():
    backend = make_synthesizer("tdsyn_enumerative")
    solve(
        """@require(f = 0) @maximize_int(f)
             def f : {v:Int | 0 <= v && v <= 1} := ?h;""",
        backend,
        budget=1,
    )
    assert {tuple(scores) for scores, _ in backend.pareto_front} == {(0.0,)}


@pytest.mark.parametrize("pooled", [False, True])
def test_program_requirement_rejects_before_objectives(pooled):
    from tests.program_specifications_test import specifications
    from aeon.synthesis.api import InvalidIndividualException

    # The failing objective must not run when the requirement is false,
    # regardless of source decorator order.
    with specifications(
        """
        @maximize_int(native "1 // 0")
        @require(f = 1)
        def f : {v:Int | 0 <= v && v <= 1} := ?h;
    """,
        pooled=pooled,
    ) as specs:
        bad = specs.candidate({specs.holes[0]: Literal(0, t_int)})
        assert not specs.validate(bad)
        good = specs.candidate({specs.holes[0]: Literal(1, t_int)})
        assert specs.validate(good)  # the unrelated failing objective is not a requirement
        with pytest.raises(InvalidIndividualException):
            specs.evaluate(bad)


def test_failing_requirement_short_circuits_objective_collection(monkeypatch):
    from aeon.synthesis import fitness_eval
    from aeon.synthesis.api import InvalidIndividualException
    from tests.program_specifications_test import specifications

    calls = []

    def collect(*args):
        calls.append(True)
        raise AssertionError("objective evaluation must not start")

    monkeypatch.setattr(fitness_eval, "_collect_expression_goals", collect)
    with specifications("@maximize_int(f) @require(false) def f : Int := ?h;", pooled=False) as specs:
        bad = specs.candidate({specs.holes[0]: Literal(0, t_int)})
        with pytest.raises(InvalidIndividualException, match="@require"):
            specs._fitness(specs.replace(bad))
    assert calls == []


@pytest.mark.parametrize("backend", ["gp", "random_search"])
def test_joint_requirements_are_mandatory(backend):
    result = solve(
        """
        def a : {v:Int | 0 <= v && v <= 1} := ?a;
        def b : {v:Int | 0 <= v && v <= 1} := ?b;
        @require(a + b = 1)
        @maximize_int(a + b)
        def score : Int := a + b;
    """,
        make_synthesizer(backend),
        budget=2,
    )
    assert all(value is not None for value in result.values())
    assert sum(value.value for value in result.values()) == 1


def test_satisfaction_only_backend_checks_requirements():
    from tests.synthesis_specifications_test import FirstValid

    backend = FirstValid()
    result = solve("@require(f = 1) def f : Int := ?h;", backend)
    assert list(result.values()) == [Literal(1, t_int)]
    assert backend.checked == [False, False, True]


@pytest.mark.parametrize("pooled", [False, True])
def test_requirements_and_objectives_share_candidate_bindings(monkeypatch, pooled):
    from aeon.core.terms import Let, Rec
    from aeon.synthesis import fitness_eval
    from aeon.synthesis.evaluation_pool import _CTX
    from tests.program_specifications_test import specifications

    calls = _CTX.Value("i", 0)
    original = fitness_eval.aeon_eval

    def counted(term, context):
        if isinstance(term, (Let, Rec)) and term.var_name.name == "shared":
            with calls.get_lock():
                calls.value += 1
        return original(term, context)

    monkeypatch.setattr(fitness_eval, "aeon_eval", counted)
    with specifications(
        """
        def f : Int := ?h;
        def shared : Int := f + 1;
        @require(shared > 0)
        @require(shared < 10)
        @maximize_int(shared * 2)
        def score : Int := shared;
    """,
        pooled=pooled,
    ) as specs:
        first = specs.candidate({specs.holes[0]: Literal(0, t_int)})
        assert specs.validate(first)
        assert specs.evaluate(first) == [2.0]
        assert calls.value == 1
        second = specs.candidate({specs.holes[0]: Literal(1, t_int)})
        assert specs.validate(second)
        assert specs.evaluate(second) == [4.0]
        assert calls.value == 2  # no values leak across candidates
        bad = specs.candidate({specs.holes[0]: Literal(-2, t_int)})
        assert not specs.validate(bad)
        assert calls.value == 3  # even a rejected candidate's checks share work
