"""Published corpus translation, independent checking and fair backend runs."""

from itertools import product
import json
import shutil

import pytest

from aeon.benchmarks.bounded_boolean.checker import (
    CheckFailure,
    check,
    check_import,
    cnf,
    core_expression,
    exhaustive_status,
    extract,
)
from aeon.benchmarks.bounded_boolean.corpus import ROOT, ae_name, emit, load_case, regenerate, verify_manifest
from aeon.benchmarks.bounded_boolean.runner import run_one, summary, completed_source
from aeon.benchmarks.bounded_boolean.verilog import VerilogError, evaluate, parse
from aeon.core.terms import Application, Let, Var
from aeon.utils.name import Name
from tests.joint_hole_synthesis_test import parse as aeon_parse, solve, fill
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer


def circuit(expression="~(y ^ (x ^ z))", inputs="x,z,y", y="y"):
    return parse(f"module formula({inputs},out); input {inputs}; output out; assign out = {expression}; endmodule", y)


def case_named(name):
    return next(c for c in verify_manifest()["cases"] if c["id"] == name)


def test_inventory_bytes_and_deterministic_regeneration(tmp_path):
    manifest = verify_manifest()
    assert manifest["inventory"]["specifications"] == manifest["inventory"]["matched"] == 38
    assert manifest["inventory"]["benchmark_y_lists"] == 53
    assert len(manifest["inventory"]["orphan_y_lists"]) == 15
    assert manifest["inventory"]["excluded_reference_y_lists"] == 52
    assert manifest["inventory"]["repository_y_lists_total"] == 105
    assert all(c["status"] == "imported" for c in manifest["cases"])
    assert len(manifest["cases"]) == 38
    shutil.copytree(ROOT, tmp_path / "copy")
    regenerated = regenerate(tmp_path / "copy")
    # JSON round trip converts schedule tuples to lists.
    assert json.loads(json.dumps(regenerated)) == manifest
    assert (tmp_path / "copy/manifest.json").read_bytes() == (ROOT / "manifest.json").read_bytes()
    for c in manifest["cases"]:
        assert (tmp_path / "copy" / c["aeon"]).read_bytes() == (ROOT / c["aeon"]).read_bytes()
    changed = tmp_path / "copy/upstream" / manifest["cases"][0]["source"]
    changed.write_bytes(changed.read_bytes() + b"\n")
    with pytest.raises(ValueError, match="hash mismatch"):
        verify_manifest(tmp_path / "copy")


def test_partitions_follow_y_list_and_not_verilog_output_port():
    c = load_case(case_named("lut1_2_2"))
    assert c.x == ("i0", "i1")
    assert c.y == ("i2", "i3")
    assert c.outputs == ("out",)
    source = emit(c, "lut1_2_2")
    assert source.index("def choose_") < source.index("def relation")
    assert "reference" not in source
    assert "native" not in source
    assert "(vi2:Bool)" not in source.split("def relation")[0]
    assert {ae_name(n) for n in ("x_y", "x$y", "x_24_y", "x24y")}.__len__() == 4


@pytest.mark.parametrize(
    "expression,expected",
    [
        ("x | z & y", lambda x, z, y: x or (z and y)),
        ("x ^ z & y", lambda x, z, y: x != (z and y)),
        ("x | z ^ y", lambda x, z, y: x or (z != y)),
        ("~x & (z | y)", lambda x, z, y: not x and (z or y)),
        ("1'b1 ^ x", lambda x, z, y: not x),
    ],
)
def test_verilog_precedence(expression, expected):
    c = circuit(expression)
    for values in product((False, True), repeat=3):
        assert evaluate(c, dict(zip(c.inputs, values))) is expected(*values)


@pytest.mark.parametrize(
    "body,y",
    [
        ("wire w; assign w = out; assign out = w;", "y"),
        ("assign out = x; assign out = y;", "y"),
        ("assign out = unknown;", "y"),
        ("wire w; assign out = w;", "y"),
        ("assign x = y; assign out = x;", "y"),
        ("assign out = x ? y : z;", "y"),
        ("assign out = x;", "y y"),
        ("assign out = x;", "missing"),
    ],
)
def test_bad_verilog_and_partitions_are_explicit(body, y):
    with pytest.raises(VerilogError, match="bad.v:"):
        parse(f"module formula(x,z,y,out); input x,z,y; output out; {body} endmodule", y, "bad.v")


def test_unused_wire_does_not_become_an_input():
    c = parse("module formula(x,y,out); input x,y; output out; wire unused; assign out=x|y; endmodule", "y")
    assert c.inputs == ("x", "y") and c.unused == ("unused",)


def test_all_published_relations_compile_and_match_original_circuits():
    for case in verify_manifest()["cases"]:
        c = load_case(case)
        driver = aeon_parse((ROOT / case["aeon"]).read_text())
        assert check_import(driver.core, c) == "equivalent", case["id"]


def test_independent_semantics_and_clause_bounds():
    c = circuit()
    correct = {"y": [[1, 2], [-1, -2]]}
    assert check(c, correct, 2)["status"] == "verified_solved"
    assert check(c, correct, 2)["exhaustive_checked"]
    assert check(c, {"y": []}, 2)["status"] == "semantic_failure"
    with pytest.raises(CheckFailure) as e:
        check(c, correct, 1)
    assert e.value.status == "bound_violation"
    for wrong in ({"y": [[3]]}, {"y": [[True]]}, {"out": []}):
        with pytest.raises(CheckFailure):
            check(c, wrong, 2)
    assert exhaustive_status(c, 1) == "bounded_unsat"
    assert exhaustive_status(c, 2) == "feasible"
    assert exhaustive_status(c, 100, limit=1) == "not_checked"


def test_partial_and_vacuous_domains_and_nullary_functions():
    c = circuit("x & ~y", "x,y")
    assert check(c, {"y": [[]]}, 1)["status"] == "verified_solved"
    assert check(circuit("0", "x,y"), {"y": []}, 0)["status"] == "verified_solved"
    assert check(circuit("~y", "y"), {"y": [[]]}, 1)["status"] == "verified_solved"
    assert exhaustive_status(circuit("~y", "y"), 0) == "bounded_unsat"
    driver = aeon_parse(emit(circuit("~y", "y"), "nullary", 1))
    result = fill(driver, solve(driver, make_synthesizer("boolean_bounded"), budget=2))
    assert extract(result, circuit("~y", "y"), 1) == {"y": [[]]}


def test_independent_normalization():
    v = ["var", 0]
    assert cnf(["bool", True], 1) == []
    assert cnf(["bool", False], 1) == [[]]
    assert cnf(["and", v, v], 1) == [[1]]
    assert cnf(["or", v, ["not", v]], 1) == []
    for expr in (["xor", v, v], ["var", 1], ["or", v, ["and", v, v]], ["not", ["and", v, v]]):
        with pytest.raises(CheckFailure):
            cnf(expr, 1)
    x, alias, witness = Name("x", 1), Name("alias", 2), Name("x", 3)
    assert core_expression(Let(alias, Var(x), Var(alias)), {x: v}) == v
    for bad in (Var(witness), Application(Var(Name("helper", 0)), Var(x))):
        with pytest.raises(CheckFailure):
            core_expression(bad, {x: v})


@pytest.mark.parametrize("backend", ["boolean_bounded", "random_search", "smt"])
def test_same_published_aeon_file_works_with_multiple_backends(backend):
    case = case_named("misc1_2_1")
    c = load_case(case)
    source = (ROOT / case["aeon"]).read_text()
    driver = aeon_parse(source)
    with driver.session.activate():
        completed = fill(driver, solve(driver, make_synthesizer(backend), budget=2))
    outputs = extract(completed, c, case["bound"])
    assert check(c, outputs, case["bound"])["status"] == "verified_solved"
    saved = completed_source(source, outputs, c)
    assert "?hole" not in saved
    assert not list(aeon_parse(saved).parse(aeon_code=saved))


def test_wrong_sampled_candidate_is_not_reported_as_success():
    c = load_case(case_named("misc1_2_1"))
    assert check(c, {c.y[0]: []}, 5)["status"] == "semantic_failure"


def test_runner_timeout_resume_and_status_denominators(tmp_path):
    case = case_named("misc1_2_1")
    first = run_one(case, "boolean_bounded", tmp_path, wall_timeout=0.01, provenance={"test_revision": "one"})
    assert first["status"] == "timeout"
    path = tmp_path / (first["key"] + ".json")
    before = path.stat().st_mtime_ns
    again = run_one(case, "boolean_bounded", tmp_path, wall_timeout=0.01, provenance={"test_revision": "one"})
    assert again == first and path.stat().st_mtime_ns == before
    changed = run_one(case, "boolean_bounded", tmp_path, wall_timeout=0.01, seed=1, provenance={"test_revision": "one"})
    assert changed["key"] != first["key"]
    assert summary([first, changed])["attempted"] == 2
    assert summary([first, changed])["statuses"] == {"timeout": 2}


def test_runner_saves_recheckable_candidate(tmp_path):
    from aeon.benchmarks.bounded_boolean.__main__ import main

    result = run_one(case_named("misc1_2_1"), "boolean_bounded", tmp_path, budget=1, wall_timeout=10)
    assert result["status"] == "verified_solved", result
    assert {"parse", "import_verification", "synthesis", "verification", "total"} <= result["timings"].keys()
    assert (tmp_path / result["candidate_file"]).exists()
    assert main(["verify", str(tmp_path / (result["key"] + ".json"))]) == 0


def test_returned_aeon_outputs_match_certificate_at_runtime():
    from aeon.backend.evaluator import eval as aeon_eval
    from aeon.core.terms import Literal
    from aeon.core.types import t_bool
    from aeon.synthesis.fitness_eval import set_program_tail
    from aeon.synthesis.identification import iterate_top_level

    case = case_named("lut1_2_2")
    c = load_case(case)
    driver = aeon_parse((ROOT / case["aeon"]).read_text())
    with driver.session.activate():
        program = fill(driver, solve(driver, make_synthesizer("boolean_bounded"), budget=3))
    outputs = extract(program, c, case["bound"])
    names = {d.var_name.name: d.var_name for d in iterate_top_level(program)}
    for bits in product((False, True), repeat=len(c.x)):
        for name, clauses in outputs.items():
            term = Var(names[f"choose_{ae_name(name)}"])
            for value in bits:
                term = Application(term, Literal(value, t_bool))
            expected = all(any(bits[abs(v) - 1] == (v > 0) for v in clause) for clause in clauses)
            assert aeon_eval(set_program_tail(program, term), driver.evaluation_ctx) is expected
