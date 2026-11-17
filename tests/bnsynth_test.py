"""Neural learning and exact verification, without selector-SAT search."""

# Optional dependency must be checked before importing the neural model.
# ruff: noqa: E402

from itertools import product
from dataclasses import asdict
from time import monotonic, sleep
import subprocess
import sys

import pytest
import z3

torch = pytest.importorskip("torch")

from aeon.synthesis.modules.bnsynth import BNSynthSynthesizer, BNSynthFailure, _Relation
from aeon.synthesis.modules.bnsynth_model import GatedCNF
from aeon.synthesis.modules.boolean_bounded import _Template
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer, synthesizer_menu_ids
from tests.boolean_bounded_test import call, direct, direct_problem
from tests.joint_hole_synthesis_test import parse, solve, fill


@pytest.mark.parametrize("n,k", [(0, 0), (0, 1), (1, 0), (1, 2), (2, 2)])
def test_discrete_network_equals_extracted_cnf(n, k):
    model = GatedCNF(n, k, torch.Generator().manual_seed(0))
    rows = list(product((False, True), repeat=n))
    inputs = torch.tensor(rows, dtype=torch.float64).reshape(len(rows), n)
    gates = k * (2 * n + 1)
    for bits in product((0.0, 1.0), repeat=gates):
        with torch.no_grad():
            model.literal_gates.copy_(torch.tensor(bits[: 2 * n * k]).reshape(k, 2 * n))
            model.clause_gates.copy_(torch.tensor(bits[2 * n * k :]))
        clauses = model.clauses()
        expected = [all(any(row[abs(v) - 1] == (v > 0) for v in c) for c in clauses) for row in rows]
        assert model(inputs).tolist() == expected
        assert len(clauses) <= k


def test_gates_receive_gradients_and_adam_learns_negation():
    torch.set_num_threads(1)
    model = GatedCNF(1, 1, torch.Generator().manual_seed(0))
    inputs = torch.tensor([[0.0], [1.0]], dtype=torch.float64)
    targets = torch.tensor([1.0, 0.0], dtype=torch.float64)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.01)
    before = model.literal_gates.detach().clone()
    for _ in range(500):
        optimizer.zero_grad()
        loss = ((model(inputs) - targets) ** 2).mean() + model.regularization()
        loss.backward()
        assert torch.isfinite(model.literal_gates.grad).all()
        optimizer.step()
        model.project()
        if model.fits(inputs, targets):
            break
    assert model.fits(inputs, targets)
    assert not torch.equal(before, model.literal_gates)
    assert model.clauses() == ((-1,),)


@pytest.mark.parametrize("expression,k", [("x", 1), ("!x", 1), ("x && y", 2), ("x || y", 1), ("x != y", 2)])
def test_actual_neural_synthesis_has_no_selector_solver_fallback(monkeypatch, expression, k):
    def forbidden(*args):
        raise AssertionError("neural search used SAT template gates")

    monkeypatch.setattr(_Template, "__init__", forbidden)
    driver = parse(f"@bounded_cnf({k}) def f(x:Bool)(y:Bool):{{r:Bool|r = ({expression})}} := ?h;")
    backend = BNSynthSynthesizer()
    completed = fill(driver, solve(driver, backend, budget=15))
    expected = {
        "x": lambda x, y: x,
        "!x": lambda x, y: not x,
        "x && y": lambda x, y: x and y,
        "x || y": lambda x, y: x or y,
        "x != y": lambda x, y: x != y,
    }[expression]
    for x, y in product((False, True), repeat=2):
        assert call(driver, completed, "f", x, y) is expected(x, y)
    assert backend.report.trained_models > 0
    assert not backend.report.enumeration_complete


@pytest.mark.parametrize("bound,value", [(0, True), (1, False)])
def test_nullary_functions_and_empty_clause(bound, value):
    driver = parse(f"@bounded_cnf({bound}) def f:{{r:Bool|r = {str(value).lower()}}} := ?h;")
    completed = fill(driver, solve(driver, BNSynthSynthesizer(), budget=10))
    assert call(driver, completed, "f") is value


def test_counterexample_is_learned_then_verified():
    driver = parse("@bounded_cnf(2) def f(x:Bool)(y:Bool):{r:Bool|r = (x != y)} := ?h;")
    backend = BNSynthSynthesizer(initial_samples=0)
    completed = fill(driver, solve(driver, backend, budget=15))
    assert backend.report.counterexamples > 0
    assert backend.report.epochs > 0
    for x, y in product((False, True), repeat=2):
        assert call(driver, completed, "f", x, y) is (x != y)


def test_coupled_outputs_and_nested_shared_calls():
    driver = parse("""
    @bounded_cnf(1) def f(x:Bool):Bool := ?a;
    @bounded_cnf(1) def g(x:Bool):Bool := ?b;
    @property(1) def law(x:Bool):Bool :=
        (f x != g x) && (f (f x) = f x) && (f (!x) = !f x);
    """)
    completed = fill(driver, solve(driver, BNSynthSynthesizer(), budget=15))
    for x in (False, True):
        assert call(driver, completed, "law", x)


def test_partial_domain_and_captured_local():
    driver = parse("@bounded_cnf(1) def f(x:{v:Bool|v}):{r:Bool|r=x} := let captured := x in ?h;")
    completed = fill(driver, solve(driver, BNSynthSynthesizer(), budget=10))
    assert call(driver, completed, "f", True)


def test_neural_learning_failure_never_claims_bounded_unsat():
    driver = parse("@bounded_cnf(1) def f(x:Bool)(y:Bool):{r:Bool|r = (x != y)} := ?h;")
    backend = BNSynthSynthesizer(epochs_per_restart=20)
    with pytest.raises(BNSynthFailure) as exc:
        solve(driver, backend, budget=2)
    assert exc.value.category == "timeout"


@pytest.mark.parametrize("phase", ["training", "verification", "validation"])
def test_neural_phases_obey_whole_run_timeout(monkeypatch, phase):
    driver = parse("@bounded_cnf(0) def f:Bool := ?h;")

    def block(*args):
        sleep(20)

    if phase == "training":
        monkeypatch.setattr(BNSynthSynthesizer, "_train", block)
    elif phase == "verification":
        monkeypatch.setattr(_Relation, "verify", block)
    else:
        import aeon.synthesis.entrypoint as entrypoint

        monkeypatch.setattr(entrypoint, "check_type", block)
    start = monotonic()
    with pytest.raises(BNSynthFailure) as exc:
        solve(driver, BNSynthSynthesizer(), budget=1)
    assert exc.value.category == "timeout"
    assert monotonic() - start < 3


def test_failed_validation_and_solver_unknown_are_not_solutions(monkeypatch):
    holes, metadata, _ = direct_problem(0, [True] * 4)
    with pytest.raises(BNSynthFailure) as exc:
        direct(BNSynthSynthesizer(), holes, metadata, validate=lambda _: False, budget=10)
    assert exc.value.category == "validation_error"
    monkeypatch.setattr(z3.Solver, "check", lambda *args: z3.unknown)
    with pytest.raises(BNSynthFailure) as exc:
        direct(BNSynthSynthesizer(), holes, metadata, budget=10)
    assert exc.value.category == "unknown"


def test_factory_and_menu_keep_torch_optional():
    assert isinstance(make_synthesizer("bnsynth"), BNSynthSynthesizer)
    assert "bnsynth" in synthesizer_menu_ids()
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            "import sys; from aeon.synthesis.modules.synthesizerfactory import make_synthesizer; make_synthesizer('bnsynth'); assert 'torch' not in sys.modules",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr


def test_seed_reproducibility_and_fresh_run_state():
    source = "@bounded_cnf(1) def f(x:Bool):{r:Bool|r = !x} := ?h;"
    driver = parse(source)
    backend = BNSynthSynthesizer(seed=7)
    a = solve(driver, backend, budget=10)
    first = asdict(backend.report)
    b = solve(driver, backend, budget=10)
    assert str(a) == str(b)
    assert first["epochs"] == backend.report.epochs
    assert first["training_rows"] == backend.report.training_rows


def test_pareto_goals_and_hard_requirements():
    driver = parse("""
        @bounded_cnf(1)
        @minimize_int(if f then 0 else 1)
        @maximize_int(if f then 0 else 1)
        def f:Bool := ?h;
    """)
    backend = BNSynthSynthesizer()
    fill(driver, solve(driver, backend, budget=2))
    assert {tuple(scores) for scores, _ in backend.pareto_front} == {(0.0, 0.0), (1.0, 1.0)}
    driver = parse("@bounded_cnf(1) @require(!f) def f:Bool := ?h;")
    completed = fill(driver, solve(driver, BNSynthSynthesizer(), budget=10))
    assert call(driver, completed, "f") is False


def test_csv_checks_reject_incorrect_networks():
    driver = parse(r'@bounded_cnf(1) @csv_data("true,false\nfalse,true") def f(x:Bool):Bool := ?h;')
    completed = fill(driver, solve(driver, BNSynthSynthesizer(), budget=10))
    for x in (False, True):
        assert call(driver, completed, "f", x) is not x


def test_different_bounds_and_shadowed_lexical_inputs():
    driver = parse("""
        @bounded_cnf(0) def f(native:Bool):Bool := ?a;
        @bounded_cnf(1) def g(native:Bool):{r:Bool|r=native} := let native := !native in ?b;
        @property(1) def law(x:Bool):Bool := (f x) && (g x = x);
    """)
    completed = fill(driver, solve(driver, BNSynthSynthesizer(), budget=10))
    for x in (False, True):
        assert call(driver, completed, "law", x)


def test_bound_violation_is_rejected_before_fitness(monkeypatch):
    driver = parse("@bounded_cnf(1) def f(x:Bool)(y:Bool):Bool := ?h;")
    monkeypatch.setattr(GatedCNF, "clauses", lambda _: ((1,), (2,)))
    with pytest.raises(BNSynthFailure, match="exceeds its CNF bound"):
        solve(driver, BNSynthSynthesizer(), budget=10)


def test_runtime_validation_failure_is_not_a_training_label(monkeypatch):
    import aeon.synthesis.entrypoint as entrypoint
    from aeon.synthesis.api import TimeoutInEvaluationException

    driver = parse(r'@bounded_cnf(0) @csv_data("true,true") def f(x:Bool):Bool := ?h;')

    def timeout(*args):
        raise TimeoutInEvaluationException()

    monkeypatch.setattr(entrypoint, "make_bundled_fitness_evaluator", lambda *args, **kwargs: timeout)
    with pytest.raises(BNSynthFailure) as exc:
        solve(driver, BNSynthSynthesizer(), budget=10)
    assert exc.value.category == "timeout"
