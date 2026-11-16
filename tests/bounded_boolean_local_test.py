"""Independent local oracles, executable certificates and failure accounting."""

import json
import shutil

import pytest

from aeon.benchmarks.bounded_boolean.checker import (
    CheckFailure,
    check,
    check_import,
    check_runtime,
    exhaustive_status,
    extract,
)
from aeon.benchmarks.bounded_boolean.corpus import (
    ROOT,
    case_hashes,
    case_source,
    digest,
    load_case,
    regenerate,
    verify_manifest,
)
from aeon.benchmarks.bounded_boolean.local import manifest, oracle_report
from aeon.benchmarks.bounded_boolean.runner import candidate_digest, completed_source, run_one, summary
from aeon.benchmarks.bounded_boolean.verification import verify_saved
from aeon.benchmarks.bounded_boolean.verilog import VerilogError, parse
from aeon.synthesis.modules.boolean_bounded import BooleanBoundedSynthesizer, BoundedBooleanFailure
from tests.joint_hole_synthesis_test import parse as aeon_parse, solve, fill


CASES = manifest()["cases"]


def local(name):
    return next(case for case in CASES if case["id"] == name)


def test_committed_oracles_are_exhaustive_and_reproducible():
    report = oracle_report()
    assert report == json.loads((ROOT / "local/oracles.json").read_text())
    assert report["all_agree"] and len(report["cases"]) == 17
    assert sum(c["minimum_certified"] for c in report["cases"]) == 15
    assert {c["minimum_bound"] for c in report["cases"] if c["task"] == "xor"} == {2}


@pytest.mark.parametrize("case", CASES, ids=lambda c: c["id"])
@pytest.mark.parametrize("bound", [0, 1, 2])
def test_backend_agrees_with_independent_local_oracles(case, bound):
    circuit = load_case(case)
    driver = aeon_parse(case_source(case, bound))
    assert check_import(driver.core, circuit) == "equivalent"
    expected = exhaustive_status(circuit, bound)
    assert expected != "not_checked"
    with driver.session.activate():
        if expected == "bounded_unsat":
            with pytest.raises(BoundedBooleanFailure) as failure:
                solve(driver, BooleanBoundedSynthesizer(), budget=5)
            assert failure.value.category == "bounded_unsat"
        else:
            completed = fill(driver, solve(driver, BooleanBoundedSynthesizer(), budget=5))
            outputs = extract(completed, circuit, bound)
            checked = check(circuit, outputs, bound)
            assert checked["status"] == "verified_solved"
            assert checked["exhaustive_checked"]
            assert check_runtime(completed, circuit, outputs, driver.evaluation_ctx)["runtime_checked"]


def test_partial_feasibility_never_weakens_total_refinements():
    partial = load_case(local("partial"))
    total = load_case(local("inconsistent_total"))
    assert partial.assignments == total.assignments
    assert check(partial, {"y": [[]]}, 1)["status"] == "verified_solved"
    assert check(total, {"y": [[]]}, 1)["status"] == "semantic_failure"
    assert exhaustive_status(partial, 1) == "feasible"
    assert exhaustive_status(total, 2) == "bounded_unsat"
    assert "{r:Bool | vx && !r}" in case_source(local("inconsistent_total"), 1)


def test_sample_success_does_not_imply_semantic_success():
    # true passes every OR sample except (false,false). Exact checking finds it.
    result = check(load_case(local("sample_trap")), {"y": []}, 1)
    assert result["status"] == "semantic_failure"
    assert not result["counterexample"]["x"] and not result["counterexample"]["z"]


def saved_candidate(tmp_path, name="sample_trap", outputs=None, bound=1):
    case = local(name)
    outputs = {"y": [[1, 2]]} if outputs is None else outputs
    source = case_source(case, bound)
    candidate = completed_source(source, outputs, load_case(case))
    path = tmp_path / "candidate.ae"
    path.write_text(candidate)
    saved = {
        "config": {
            "task": name,
            "suite": "local",
            "schema_version": 2,
            "bound": bound,
            "source_sha256": digest(source.encode()),
            **case_hashes(case),
        },
        "outputs": outputs,
        "candidate_sha256": candidate_digest(outputs),
        "candidate_file": path.name,
        "candidate_file_sha256": digest(path.read_bytes()),
    }
    return saved, path


def test_saved_program_is_verified_and_executed(tmp_path):
    saved, _ = saved_candidate(tmp_path)
    result = verify_saved(saved, tmp_path)
    assert result["status"] == "verified_solved"
    assert result["verification_scope"] == "program_and_certificate"
    assert result["runtime_evaluations"] == 4


@pytest.mark.parametrize("update_hash", [False, True])
def test_valid_certificate_cannot_mask_changed_program(tmp_path, update_hash):
    saved, path = saved_candidate(tmp_path)
    path.write_text(path.read_text().replace("((vx || vz))", "true"))
    if update_hash:
        saved["candidate_file_sha256"] = digest(path.read_bytes())
    with pytest.raises(CheckFailure, match="disagrees|hash mismatch"):
        verify_saved(saved, tmp_path)


def test_missing_candidate_requires_explicit_certificate_only_check(tmp_path):
    saved, path = saved_candidate(tmp_path)
    path.unlink()
    with pytest.raises(CheckFailure, match="missing"):
        verify_saved(saved, tmp_path)
    assert verify_saved(saved, tmp_path, certificate_only=True)["verification_scope"] == "certificate_only"
    del saved["candidate_file"]
    with pytest.raises(CheckFailure, match="missing"):
        verify_saved(saved, tmp_path)


def test_runtime_crosscheck_detects_translation_disagreement(tmp_path):
    saved, path = saved_candidate(tmp_path)
    driver = aeon_parse(path.read_text())
    circuit = load_case(local("sample_trap"))
    # Simulate a mistaken extraction/normalization, even with a legal shape.
    extract(driver.core, circuit, 1)
    with pytest.raises(CheckFailure, match="execution disagrees"):
        check_runtime(driver.core, circuit, {"y": []}, driver.evaluation_ctx)


@pytest.mark.parametrize("replacement", ["(if vx then true else vz)", "(vx != vz)", "?unfilled"])
def test_non_cnf_saved_program_cannot_hide_in_a_valid_certificate(tmp_path, replacement):
    saved, path = saved_candidate(tmp_path)
    path.write_text(path.read_text().replace("((vx || vz))", replacement))
    saved["candidate_file_sha256"] = digest(path.read_bytes())
    with pytest.raises(CheckFailure):
        verify_saved(saved, tmp_path)


def test_other_output_is_not_a_permitted_literal():
    source = case_source(local("coupled"), 1).replace("?hole_vy", "true").replace("?hole_vw", "choose_vy vx")
    driver = aeon_parse(source)
    with pytest.raises(CheckFailure, match="helper, witness"):
        extract(driver.core, load_case(local("coupled")), 1)


def test_candidate_cannot_narrow_its_declared_input_domain():
    source = case_source(local("identity"), 1).replace("(vx:Bool)", "(vx:{b:Bool | b})", 1)
    source = source.replace("?hole_vy", "vx")
    # Omit the calling law so Aeon's own call-site check does not reject first;
    # this exercises the independent signature checker directly.
    driver = aeon_parse(source.split("@property")[0])
    with pytest.raises(CheckFailure, match="exactly the declared Boolean inputs"):
        extract(driver.core, load_case(local("identity")), 1)


def test_empty_y_list_is_a_diagnostic():
    with pytest.raises(VerilogError, match="empty.v:.*Y list"):
        parse("module f(x,out); input x; output out; assign out=x; endmodule", "", "empty.v")


def test_inventory_counts_matches_even_when_translation_is_unsupported(tmp_path):
    shutil.copytree(ROOT, tmp_path / "copy")
    root = tmp_path / "copy"
    first = verify_manifest()["cases"][0]
    source = root / "upstream" / first["source"]
    source.write_text("unsupported verilog")
    report = regenerate(root)
    assert report["inventory"]["matched"] == 38
    assert len(report["inventory"]["orphan_y_lists"]) == 15
    assert len(report["inventory"]["repository_lists_without_specification"]) == 67
    assert next(c for c in report["cases"] if c["id"] == first["id"])["status"] == "unsupported"
    (root / "inventory-provenance.json").write_text("{}")
    with pytest.raises(ValueError, match="provenance hash"):
        verify_manifest(root)


def test_import_failures_stay_in_runner_denominator(tmp_path):
    case = {"id": "missing", "source": "absent.v", "y_file": "absent.txt"}
    result = run_one(case, "boolean_bounded", tmp_path / "runs", root=tmp_path, provenance={"test": True})
    assert result["status"] == "translation_failure"
    assert summary([result])["statuses"] == {"translation_failure": 1}


def test_resume_recreates_a_missing_saved_program(tmp_path):
    case = local("true")
    kwargs = {"bound": 0, "budget": 2, "wall_timeout": 15, "provenance": {"test": True}}
    first = run_one(case, "boolean_bounded", tmp_path, **kwargs)
    assert first["status"] == "verified_solved", first
    candidate = tmp_path / first["candidate_file"]
    candidate.unlink()
    again = run_one(case, "boolean_bounded", tmp_path, **kwargs)
    assert again["key"] == first["key"]
    assert candidate.is_file()
    assert verify_saved(again, tmp_path)["status"] == "verified_solved"


def test_bounded_unsat_is_certified_only_by_completed_enumeration(tmp_path):
    result = run_one(local("xor"), "boolean_bounded", tmp_path, bound=1, budget=2, wall_timeout=15)
    assert result["status"] == "bounded_unsat", result
    assert result["certification"] == "exhaustive"
    assert "outputs" not in result


def test_oracle_does_not_call_a_solver_or_backend(monkeypatch):
    import z3

    def forbidden(*args, **kwargs):
        raise AssertionError("oracle called a solver")

    monkeypatch.setattr(z3, "Solver", forbidden)
    monkeypatch.setattr(BooleanBoundedSynthesizer, "synthesize_joint", forbidden)
    assert oracle_report()["all_agree"]


def test_worker_classifies_a_malformed_partition_as_translation_failure(tmp_path):
    case = next(c for c in verify_manifest()["cases"] if c["id"] == "misc1_2_1")
    root = tmp_path / "corpus"
    for relative in (case["aeon"], "upstream/" + case["source"], "upstream/" + case["y_file"]):
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, path)
    (root / "upstream" / case["y_file"]).write_text("unknown_witness")
    result = run_one(case, "boolean_bounded", tmp_path / "runs", root=root, wall_timeout=15)
    assert result["status"] == "translation_failure", result
    assert "Y list" in result["reason"]
    assert "parse" in result["timings"]


def test_bound_variants_preserve_the_original_importer_source():
    from aeon.benchmarks.bounded_boolean.corpus import emit

    for case in verify_manifest()["cases"]:
        for bound in (0, 2, 5):
            assert case_source(case, bound) == emit(load_case(case), case["id"], bound)
