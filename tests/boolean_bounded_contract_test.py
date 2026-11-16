"""Bounded search must distinguish logical infeasibility from failed checks."""

from itertools import combinations, product
from math import inf, nan

import pytest
import z3

from aeon.benchmarks.bounded_boolean.checker import cnf, core_expression
from aeon.core.terms import Literal
from aeon.core.types import t_bool, t_int
from aeon.synthesis.api import InvalidIndividualException, TimeoutInEvaluationException
from aeon.synthesis.decorators import Goal
from aeon.synthesis.modules.boolean_bounded import BooleanBoundedSynthesizer, BoundedBooleanFailure, _Template
from aeon.synthesis.solver_problem import SolverHole
from aeon.utils.name import Name
from tests.boolean_bounded_test import call, direct, direct_problem
from tests.joint_hole_synthesis_test import parse, solve, fill


@pytest.mark.parametrize("failure", ["invalid", "timeout", "nan", "wrong_length"])
def test_objective_failure_cannot_prove_bounded_unsat(failure):
    holes, metadata, _ = direct_problem(0, [True] * 4)
    metadata[Name("joint", 0)]["goals"] = [Goal(True, 1, Name("cost", 900))]

    def evaluate(_):
        if failure == "invalid":
            raise InvalidIndividualException("objective could not be evaluated")
        if failure == "timeout":
            raise TimeoutInEvaluationException("objective timed out")
        return [nan] if failure == "nan" else []

    backend = BooleanBoundedSynthesizer()
    with pytest.raises(BoundedBooleanFailure) as exc:
        direct(backend, holes, metadata, evaluate=evaluate)
    assert exc.value.category == ("timeout" if failure == "timeout" else "validation_error")
    assert backend.report.status == exc.value.category


def test_csv_metadata_does_not_turn_type_rejection_into_unsat():
    holes, metadata, _ = direct_problem(0, [True] * 4)
    metadata[Name("joint", 0)]["goals"] = [Goal(True, 1, Name("observations", 900), "csv")]
    backend = BooleanBoundedSynthesizer()
    with pytest.raises(BoundedBooleanFailure) as exc:
        direct(backend, holes, metadata, validate=lambda _: False)
    assert exc.value.category == "validation_error"


@pytest.mark.parametrize("phase", ["types", "runtime_timeout", "runtime_error", "property_mismatch"])
def test_joint_gate_preserves_failure_reason_in_presence_of_csv(monkeypatch, phase):
    import aeon.synthesis.entrypoint as entrypoint

    driver = parse(
        r'@bounded_cnf(0) @csv_data("true,true") def f(x:Bool):Bool := ?h;'
        " @property(1) def law(x:Bool):Bool := f x;"
    )
    if phase == "types":
        monkeypatch.setattr(entrypoint, "check_type", lambda *args: False)
    else:
        original = entrypoint.make_bundled_fitness_evaluator

        def make_fitness(goals, *args, **kwargs):
            if any(g.kind == "property" for g in goals):

                def failing(_):
                    if phase == "runtime_timeout":
                        raise TimeoutInEvaluationException()
                    if phase == "runtime_error":
                        raise ValueError("injected runtime check error")
                    return [1.0] * sum(g.length for g in goals)

                return failing
            return original(goals, *args, **kwargs)

        monkeypatch.setattr(entrypoint, "make_bundled_fitness_evaluator", make_fitness)
    with pytest.raises(BoundedBooleanFailure) as exc:
        solve(driver, BooleanBoundedSynthesizer(), budget=3)
    assert exc.value.category == ("timeout" if phase == "runtime_timeout" else "validation_error")


@pytest.mark.parametrize("bound", [0, 1, 2])
@pytest.mark.parametrize("n", [0, 1, 2])
def test_symmetry_breaking_preserves_every_normalized_cnf(n, bound):
    params = tuple((Name("input", 200 + i), t_bool) for i in range(n))
    schema = SolverHole(Name("hole", 100), Name("unknown", 101), params, (), t_bool)
    template = _Template(schema, bound, 0)
    solver = z3.Solver()
    solver.add(template.constraints())
    clauses = [tuple(sign * (i + 1) for i, sign in enumerate(signs) if sign) for signs in product((0, 1, -1), repeat=n)]
    expected = set()
    for size in range(min(bound, len(clauses)) + 1):
        for selected in combinations(clauses, size):
            expected.add(((),) if () in selected else tuple(sorted(tuple(sorted(c)) for c in selected)))
    found = set()
    while solver.check() == z3.sat:
        model = solver.model()
        expression = core_expression(template.extract(model), {name: ["var", i] for i, (name, _) in enumerate(params)})
        certificate = tuple(tuple(c) for c in cnf(expression, n))
        assert certificate not in found, "selector symmetry produced the same normalized CNF twice"
        found.add(certificate)
        solver.add(z3.Or([s != model.eval(s, model_completion=True) for s in template.selectors]))
    assert found == expected


@pytest.mark.parametrize("bound,feasible", [(0, False), (1, True)])
def test_source_requirements_are_enumerated_as_hard_constraints(bound, feasible):
    driver = parse(f"@bounded_cnf({bound}) @require(!f) def f:Bool := ?h;")
    backend = BooleanBoundedSynthesizer()
    if not feasible:
        with pytest.raises(BoundedBooleanFailure) as exc:
            solve(driver, backend, budget=3)
        assert exc.value.category == "bounded_unsat"
    else:
        program = fill(driver, solve(driver, backend, budget=3))
        assert call(driver, program, "f") is False


@pytest.mark.parametrize("budget", [inf, nan])
def test_nonfinite_budgets_are_controlled_capability_errors(budget):
    from aeon.synthesis.api import UnsupportedSynthesisGoal

    holes, metadata, _ = direct_problem(0, [True] * 4)
    with pytest.raises(UnsupportedSynthesisGoal, match="finite"):
        direct(BooleanBoundedSynthesizer(), holes, metadata, budget=budget)


def test_memory_exhaustion_has_its_own_failure_category(monkeypatch):
    holes, metadata, _ = direct_problem(0, [True] * 4)

    def fail(*args):
        raise MemoryError("injected memory exhaustion")

    monkeypatch.setattr(_Template, "extract", fail)
    with pytest.raises(BoundedBooleanFailure) as exc:
        direct(BooleanBoundedSynthesizer(), holes, metadata)
    assert exc.value.category == "resource_limit"


def test_different_output_bounds_and_shared_skolem_law():
    driver = parse("""
        @bounded_cnf(0) def f(x:Bool):Bool := ?hf;
        @bounded_cnf(1) def g(x:Bool):Bool := ?hg;
        @property(1) def law(x:Bool):Bool := (f x != g x) = x;
    """)
    backend = BooleanBoundedSynthesizer()
    program = fill(driver, solve(driver, backend, budget=3))
    for bit in (False, True):
        assert call(driver, program, "f", bit) is True
        assert call(driver, program, "g", bit) is not bit


def test_invalid_extracted_type_is_never_a_csv_counterexample(monkeypatch):
    driver = parse(r'@bounded_cnf(1) @csv_data("true,true") def f(x:Bool):Bool := ?h;')
    monkeypatch.setattr(_Template, "extract", lambda *args: Literal(1, t_int))
    with pytest.raises(BoundedBooleanFailure) as exc:
        solve(driver, BooleanBoundedSynthesizer(), budget=3)
    assert exc.value.category == "validation_error"


def test_context_preparation_is_charged_once_to_the_deadline(monkeypatch):
    import time
    import aeon.synthesis.typeclasses as typeclasses
    from aeon.synthesis.joint import JointCandidate

    driver = parse("@bounded_cnf(0) def f:Bool := ?h;")
    backend = BooleanBoundedSynthesizer()
    backend._in_worker = True  # Inspect entrypoint accounting, not process timing.
    clock = [time.monotonic()]
    monkeypatch.setattr(time, "monotonic", lambda: clock[0])
    prepare = typeclasses.prepare_typeclass_components

    def prepare_with_cost(*args, **kwargs):
        result = prepare(*args, **kwargs)
        clock[0] += 0.25
        return result

    def synthesize(*args):
        assert args[5] == pytest.approx(0.75)
        return JointCandidate((Literal(True, t_bool),))

    monkeypatch.setattr(typeclasses, "prepare_typeclass_components", prepare_with_cost)
    monkeypatch.setattr(backend, "synthesize_joint", synthesize)
    assert next(iter(solve(driver, backend, budget=1).values())) == Literal(True, t_bool)


def test_native_required_specifications_are_explicitly_unsupported():
    from aeon.synthesis.api import UnsupportedSynthesisGoal

    driver = parse('@bounded_cnf(1) @require(native "True") def f:Bool := ?h;')
    with pytest.raises(UnsupportedSynthesisGoal, match="native specifications"):
        solve(driver, BooleanBoundedSynthesizer(), budget=3)


def test_name_identity_is_preserved_for_shadowed_boolean_inputs():
    driver = parse("@bounded_cnf(1) def f(x:Bool):{r:Bool | r = x} := let x := !x in ?h;")
    program = fill(driver, solve(driver, BooleanBoundedSynthesizer(), budget=3))
    for value in (False, True):
        assert call(driver, program, "f", value) is value


@pytest.mark.parametrize("name", ["native", "native_import", "uninterpreted", "print"])
def test_local_name_is_not_the_primitive(name):
    driver = parse(f"@bounded_cnf(1) def f({name}:Bool):{{r:Bool | r = {name}}} := ?h;")
    program = fill(driver, solve(driver, BooleanBoundedSynthesizer(), budget=3))
    for value in (False, True):
        assert call(driver, program, "f", value) is value


def test_local_names_do_not_receive_trusted_native_contracts():
    from aeon.core.terms import Var
    from aeon.typechecking.typeinfer import _is_trusted_native_value

    for name in ("native", "native_import", "uninterpreted"):
        assert _is_trusted_native_value(Var(Name(name, 0)))
        assert not _is_trusted_native_value(Var(Name(name, 901)))


def test_reports_distinguish_first_solution_from_complete_enumeration():
    backend = BooleanBoundedSynthesizer()
    solve(parse("@bounded_cnf(1) def f:Bool := ?h;"), backend, budget=3)
    assert backend.report.validated_candidates == 1
    assert backend.report.solver_calls == 2
    assert not backend.report.enumeration_complete
    driver = parse("@bounded_cnf(1) @minimize_int(if f then 0 else 1) def f:Bool := ?h;")
    program = fill(driver, solve(driver, backend, budget=3))
    assert call(driver, program, "f") is True
    assert backend.report.validated_candidates == 2
    assert backend.report.enumeration_complete
    assert backend.report.solver_calls == 5
    # Fresh state on a reused backend, including enumeration and objective data.
    solve(parse("@bounded_cnf(0) def f:Bool := ?h;"), backend, budget=3)
    assert not backend.report.enumeration_complete and not backend.pareto_front


@pytest.mark.parametrize("expression", ["native \"float('nan')\"", 'native "1 // 0"'])
def test_source_objective_errors_are_not_infeasibility(expression):
    driver = parse(f"@bounded_cnf(0) @minimize_float({expression}) def f:Bool := ?h;")
    with pytest.raises(BoundedBooleanFailure) as exc:
        solve(driver, BooleanBoundedSynthesizer(), budget=3)
    assert exc.value.category == "validation_error"
