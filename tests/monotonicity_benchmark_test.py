"""Universal monotonicity contracts, not property-based input sampling."""

import json
import re
from dataclasses import asdict

import pytest
from z3 import unknown

from aeon.benchmarks.monotonicity import DEFAULT_TASK_DIR, TASKS, MonotonicityBenchmark, main
from aeon.core.terms import Literal
from aeon.core.types import t_int
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.modules.enumerative import EnumerativeSynthesizer
from aeon.verification import smt


REFERENCES = {
    "nondecreasing": "0",
    "strict": "x",
    "identity": "x",
    "shift": "x + 1",
    "relu": "if x <= 0 then 0 else x",
}


@pytest.mark.parametrize("task", TASKS)
def test_references_prove_all_refinements(task):
    benchmark = MonotonicityBenchmark(task)
    report = benchmark.verify(REFERENCES[task])
    assert report.status == "proved" and report.accepted
    assert "?body" not in benchmark.completed_source(report.candidate)
    json.dumps(asdict(report))


def test_decreasing_candidate_has_a_concrete_ordered_pair():
    report = MonotonicityBenchmark("nondecreasing").verify("0 - x")
    assert report.status == "disproved" and not report.accepted
    witness = next(f.counterexample for f in report.failures if f.counterexample)
    x1 = int(re.search(r"x1 = (-?\d+)", witness).group(1))
    x2 = int(re.search(r"x2 = (-?\d+)", witness).group(1))
    assert -5 <= x1 < x2 <= 5
    assert -x1 > -x2


def test_endpoint_drop_is_rejected_even_when_interior_is_increasing():
    report = MonotonicityBenchmark("nondecreasing").verify("if x = 5 then (0 - 100) else x")
    assert report.status == "disproved" and not report.accepted
    witness = next(f.counterexample for f in report.failures if f.counterexample)
    assert "x2 = 5" in witness


def test_negative_slope_on_positive_domain_is_not_accepted():
    assert not MonotonicityBenchmark("identity").verify("0 - x").accepted


def test_constants_are_monotone_but_not_strict_or_endpoint_solutions():
    assert MonotonicityBenchmark("nondecreasing").verify("3").accepted
    assert not MonotonicityBenchmark("strict").verify("3").accepted
    assert not MonotonicityBenchmark("identity").verify("3").accepted


def test_equal_inputs_are_included_in_nondecreasing_contract():
    # A wrongly strict output predicate with <= input order would reject x.
    assert MonotonicityBenchmark("nondecreasing").verify("x").accepted


@pytest.mark.parametrize(
    "candidate",
    [
        "x / 0",
        "x / (x - x)",
        "x / 2",
        "x % 2",
        "x * x",
        "x + 1.0",
        'native "42"',
        "f x",
        "?another",
        "x1",
        "x2",
        "let y := x in y",
    ],
)
def test_unsupported_or_partial_expressions_are_never_proofs(candidate):
    report = MonotonicityBenchmark("nondecreasing").verify(candidate)
    assert report.status == "unsupported" and not report.accepted


def test_type_errors_are_not_proofs():
    assert not MonotonicityBenchmark("nondecreasing").verify("true").accepted


def test_affine_and_piecewise_linear_candidates_are_supported():
    benchmark = MonotonicityBenchmark("nondecreasing")
    assert benchmark.verify("2 * x + 1").accepted
    assert benchmark.verify("x * (1 + 2)").accepted
    assert benchmark.verify("if x < 0 then (0 - 1) else 1").accepted
    assert not benchmark.verify("if x < 0 then 1 else (0 - 1)").accepted


def test_domain_limits_are_not_accidentally_global():
    # Identity task's domain is [0,4]. A drop outside it is irrelevant.
    benchmark = MonotonicityBenchmark("identity")
    assert benchmark.verify("if x < 0 then 100 else x").accepted


def test_unknown_solver_result_is_unproven_without_counterexample(monkeypatch):
    benchmark = MonotonicityBenchmark("nondecreasing")
    monkeypatch.setattr(smt.s, "check", lambda: unknown)
    report = benchmark.verify("x")
    assert report.status == "unproven" and not report.accepted
    assert all(f.counterexample is None for f in report.failures)
    smt.clear_smt_caches()


def test_empty_domain_cannot_vacuously_satisfy_benchmark(tmp_path):
    source = (DEFAULT_TASK_DIR / "identity.ae").read_text()
    source = source.replace("0 <= v && v <= 4", "5 <= v && v <= 4")
    # Drop the now-out-of-domain endpoint calls to isolate the empty domain.
    source = source.split("def endpoints")[0]
    (tmp_path / "identity.ae").write_text(source)
    with pytest.raises(ValueError, match="empty"):
        MonotonicityBenchmark("identity", tmp_path)


def test_search_scope_does_not_contain_pair_inputs_or_trusted_helpers():
    names = {name.name for name, _ty in MonotonicityBenchmark("identity").ctx.vars()}
    assert "x" in names
    assert not names & {"x1", "x2", "f", "native", "native_import", "monotonicity", "endpoints"}


@pytest.mark.parametrize("task", ["nondecreasing", "strict", "identity", "shift"])
def test_actual_enumerative_synthesis_is_proved(task):
    benchmark = MonotonicityBenchmark(task)
    result = benchmark.synthesize(budget=10)
    assert result is not None and result.accepted
    assert benchmark.verify(result.candidate).accepted


def test_search_rejects_decreasing_candidate_before_accepting_identity(monkeypatch):
    import aeon.synthesis.modules.enumerative as enumerative
    from aeon.core.terms import Var
    from aeon.utils.ast_helpers import mk_binop

    benchmark = MonotonicityBenchmark("identity")
    x_name = next(n for n, _t in benchmark.ctx.vars() if n.name == "x")
    decreasing = mk_binop("-", Literal(0, t_int), Var(x_name))
    monkeypatch.setattr(enumerative, "iter_candidates", lambda *a, **k: iter([decreasing, Var(x_name)]))
    result = benchmark.synthesize()
    assert result is not None and result.candidate == "x"
    assert not benchmark._results["0 - x"].accepted


def test_backend_cannot_bypass_the_final_proof_gate(monkeypatch):
    monkeypatch.setattr(EnumerativeSynthesizer, "synthesize", lambda *a, **k: Literal(0, t_int))
    assert MonotonicityBenchmark("identity").synthesize() is None


@pytest.mark.parametrize("mode", ["none", "exception"])
def test_no_solution_is_reported_without_crashing(monkeypatch, mode):
    def no_solution(*args, **kwargs):
        if mode == "exception":
            raise SynthesisNotSuccessful
        return None

    monkeypatch.setattr(EnumerativeSynthesizer, "synthesize", no_solution)
    assert MonotonicityBenchmark("identity").synthesize() is None


@pytest.mark.parametrize("budget", [0, -1, float("inf"), float("nan")])
def test_budget_must_be_positive_and_finite(budget):
    with pytest.raises(ValueError, match="Budget"):
        MonotonicityBenchmark("identity").synthesize(budget=budget)


def test_cli_outputs_a_machine_readable_proof(monkeypatch, capsys):
    monkeypatch.setattr("sys.argv", ["monotonicity", "--task", "identity", "--candidate", "x"])
    assert main() == 0
    report = json.loads(capsys.readouterr().out)
    assert report["task"] == "identity" and report["status"] == "proved"


def test_cli_nonzero_on_rejection(monkeypatch, capsys):
    monkeypatch.setattr("sys.argv", ["monotonicity", "--task", "identity", "--candidate", "0 - x"])
    assert main() == 2
    assert json.loads(capsys.readouterr().out)["status"] != "proved"
