"""Executable specifications, provenance, and translator regression coverage."""

from __future__ import annotations

import gzip
import hashlib
import io
import json
import tarfile
from collections import Counter
from pathlib import Path

import pytest

from aeon.benchmarks import paper_io
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from scripts.paper_benchmarks.__main__ import extract_archive
from scripts.paper_benchmarks.common import sexprs
from scripts.paper_benchmarks.invariants import expression
from scripts.paper_benchmarks.memoization import Problem, evaluate, states
from scripts.paper_benchmarks.ml import translate
from scripts.paper_benchmarks.para import Interpreter, definitions

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "examples/papers"
MANIFEST = json.loads((CORPUS / "manifest.json").read_text())


def compile_source(source):
    driver = AeonDriver(
        AeonConfig(synthesizer="random_search", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    )
    errors = driver.parse(aeon_code=source)
    assert not errors, errors
    return driver


def test_manifest_is_complete_and_checksums_match():
    paths = [row["path"] for row in MANIFEST]
    assert len(paths) == len(set(paths))
    assert set(paths) == {p.relative_to(CORPUS).as_posix() for p in CORPUS.rglob("*.ae")}
    counts = Counter(row["suite"].split("/")[0] for row in MANIFEST)
    assert counts == {
        "l2": 44,
        "smyth": 164,
        "dreamcoder": 220,
        "burst": 135,
        "trio": 120,
        "trio-jfp": 130,
        "guide": 80,
        "para": 52,
        "hoogle": 44,
        "hectare": 64,
        "clause2inv": 366,
        "asac": 136,
        "synmem": 64,
    }
    for row in MANIFEST:
        assert hashlib.sha256((CORPUS / row["path"]).read_bytes()).hexdigest() == row["sha256"], row["path"]
        assert len(row["source_sha256"]) == 64


@pytest.mark.parametrize("row", MANIFEST, ids=lambda row: row["path"])
def test_paper_program_compiles_with_a_synthesis_target(row):
    driver = compile_source((CORPUS / row["path"]).read_text())
    assert driver.has_synth()
    if row["specification"] != "type-inhabitation":
        assert any(
            isinstance(meta, dict) and ("goals" in meta or "property" in meta) for meta in driver.metadata.values()
        )


def test_functional_libraries_execute():
    driver = compile_source("""
open Seq
open Maybe
open Pair
open Functional
@example(Seq.reverse (Seq.cons 1 (Seq.cons 2 (Seq.nil{Int}))) = Seq.cons 2 (Seq.cons 1 (Seq.nil{Int})))
@example(Functional.filter (fun x => x > 1) (Seq.cons 1 (Seq.cons 2 (Seq.nil{Int}))) = Seq.cons 2 (Seq.nil{Int}))
@example(Functional.nth 2 (Seq.cons 1 (Seq.nil{Int})) = (Maybe.none{Int}))
@example(Functional.sortBy (fun x => fun y => x < y) (Seq.cons 2 (Seq.cons 1 (Seq.cons 2 (Seq.nil{Int})))) = Seq.cons 1 (Seq.cons 2 (Seq.cons 2 (Seq.nil{Int}))))
def witness (x:Int) : Int := x;
""")
    assert driver.run_tests() == []


@pytest.mark.parametrize(
    "path,body",
    [
        ("l2/length.ae", "Seq.length arg0"),
        ("para/list_map.ae", "Seq.map arg0 arg1"),
        ("trio/io/nat_pred.ae", "match arg0 with | C_O => T_nat.C_O | C_S previous => previous"),
    ],
)
def test_published_examples_accept_known_correct_implementations(path, body):
    source = (CORPUS / path).read_text()
    correct = compile_source(source.replace("?hole", body))
    assert correct.run_tests() == []
    if path == "l2/length.ae":
        wrong = compile_source(source.replace("?hole", "0"))
        assert wrong.run_tests()


def test_exact_smt_division_and_real_to_integer_coercion():
    driver = compile_source("""
open SMTArithmetic
@example(smt_div (0 - 3) 2 = (0 - 2))
@example(smt_mod (0 - 3) (0 - 2) = 1)
@example(smt_div (0 - 3) (0 - 2) = 2)
@example(rationalFloor (rationalDiv (rational (0 - 3)) (rational 2)) = (0 - 2))
@example(rationalEq (rationalDiv (rational 1) (rational 3)) (rationalDiv (rational 2) (rational 6)))
def witness (x:Int) : Int := x;
""")
    assert driver.run_tests() == []
    rendered = expression(sexprs("(= (mod (/ count 2) 2) 0)")[0])
    assert "rationalFloor" in rendered and "smt_real_div" not in rendered


def test_memoization_scoring_penalizes_unsound_collisions():
    driver = compile_source("""
open Seq
open Pair
open Memoization
def cases : (Seq (Pair (Seq Int) Int)) := Seq.cons (Pair.mk (Seq.nil{Int}) 0) (Seq.cons (Pair.mk (Seq.cons 1 (Seq.nil{Int})) 1) (Seq.nil{(Pair (Seq Int) Int)}));
@example(Memoization.partitionScore Seq.length cases = 2)
@example(Memoization.partitionScore (fun prefix => 0) cases = 100001)
def witness (x:Int) : Int := x;
""")
    assert driver.run_tests() == []


def test_contest_dataset_integrity_and_candidate_failures(tmp_path, monkeypatch):
    monkeypatch.setattr(paper_io, "DATA_ROOT", tmp_path)
    payload = json.dumps([["1 2", "3"], ["2 4", "6"]]).encode()
    checksum = hashlib.sha256(payload).hexdigest()
    (tmp_path / "sample.json.gz").write_bytes(gzip.compress(payload))
    paper_io.load_cases.cache_clear()
    assert paper_io.failures("sample", checksum, lambda s: str(sum(map(int, s.split()))) + "\n") == 0
    assert paper_io.failures("sample", checksum, lambda s: "0") == 2
    assert paper_io.failures("sample", checksum, lambda s: 1 / 0) == 2
    with pytest.raises(ValueError, match="checksum"):
        paper_io.load_cases("sample", "0" * 64)
    with pytest.raises(FileNotFoundError):
        paper_io.load_cases("missing", checksum)
    with pytest.raises(ValueError, match="not a path"):
        paper_io.load_cases("../sample", checksum)
    paper_io.load_cases.cache_clear()


def test_archive_extraction_rejects_paths_and_symlinks_outside_root(tmp_path):
    for name, target in [("repo/../../escape", ""), ("repo/link", "../../escape")]:
        archive = tmp_path / "bad.tar.gz"
        with tarfile.open(archive, "w:gz") as bundle:
            member = tarfile.TarInfo(name)
            if target:
                member.type = tarfile.SYMTYPE
                member.linkname = target
            else:
                member.size = 1
            bundle.addfile(member, None if target else io.BytesIO(b"x"))
        with pytest.raises(ValueError, match="Unsafe"):
            extract_archive(archive, tmp_path / "output")


def test_docker_source_extraction_applies_whiteouts_without_running_image(tmp_path):
    def archive_bytes(files):
        output = io.BytesIO()
        with tarfile.open(fileobj=output, mode="w") as bundle:
            for name, data in files.items():
                member = tarfile.TarInfo(name)
                member.size = len(data)
                bundle.addfile(member, io.BytesIO(data))
        return output.getvalue()

    first = archive_bytes({"home/SynMem/benchmarks/old.h": b"old"})
    second = archive_bytes(
        {
            "home/SynMem/benchmarks/new.h": b"new",
            "home/SynMem/benchmarks/.wh..wh..opq": b"",
            "usr/bin/unrelated": b"not extracted",
        }
    )
    image = tmp_path / "image.tar"
    image.write_bytes(
        archive_bytes(
            {
                "manifest.json": json.dumps([{"Layers": ["first/layer.tar", "second/layer.tar"]}]).encode(),
                "first/layer.tar": first,
                "second/layer.tar": second,
            }
        )
    )
    extract_archive(image, tmp_path / "sources", "docker")
    assert (tmp_path / "sources/benchmarks/new.h").read_bytes() == b"new"
    assert list((tmp_path / "sources").rglob("*.*")) == [tmp_path / "sources/benchmarks/new.h"]


def test_ml_nested_pattern_fallthrough():
    source = """
type nat = | O | S of nat
let classify = fix (classify : nat -> nat) = fun (n:nat) -> match n with
| S (S x) -> S O
| S x -> O
| O -> O
;;
synth nat -> nat satisfying [0] -> 0, [1] -> 0, [2] -> 1
"""
    code, _, _ = translate(source)
    driver = compile_source(code.replace("?hole", "classify arg0"))
    assert driver.run_tests() == []


def test_para_truth_and_reference_interpretation():
    source = "(defproblem pick (fixnum) fixnum (n) (if n 7 8))"
    interpreter = Interpreter(source)
    ((_, _, _, _, params, *body),) = definitions(source, "defproblem")
    fn = interpreter.function(params.items, body[-1], {}, recursive=True)
    assert fn(0) == 7  # Common Lisp's zero is true.


def test_synmem_residual_equivalence_is_exhaustive_for_small_instances():
    source = """
n_id = new_parameter("n", {1, INF});
x_id = new_var_list("x", n_id + INF, {0,1});
i_id = new_var("i", {-INF,INF});
v = new constval(x_id + INF);
at = new atom_term(string_to_op("Call_list_to_value_or_Var"), {v,new constval(0)});
c = new atom_term(string_to_op("Equal"), {at,new constval(1)});
add_constraint(c);
"""
    problem = Problem.parse(source)
    params, cases = states(problem, 0)
    assert params == [3] and len(cases) == 15
    classes = {tuple(prefix): label for prefix, label in cases}
    assert classes[(0, 0)] == classes[(0, 1)]
    assert classes[(0, 0)] != classes[(1, 0)]
    assert evaluate(problem.constraints[0], {"x_id": [1, 0, 0]}) == 1
