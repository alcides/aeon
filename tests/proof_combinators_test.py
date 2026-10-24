"""Checked paper ports, false-proof controls, and proof-notation compatibility."""

import json
from pathlib import Path

import pytest

from aeon.errors import LiquidTypeCheckingFailedRelation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

ROOT = Path(__file__).resolve().parents[1] / "examples" / "proofs"


def compile_source(tmp_path, source, *, no_main=True):
    path = tmp_path / "proof.ae"
    path.write_text(source)
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=no_main))
    errors = list(driver.parse(filename=str(path), aeon_code=source))
    return driver, errors


def test_paper_proofs_and_runtime_examples(tmp_path):
    driver, errors = compile_source(tmp_path, (ROOT / "Paper.ae").read_text(), no_main=False)
    assert not errors, errors
    assert not driver.has_synth(), "Every proof must be complete, with no synthesis holes"
    assert driver.run() == 42


def test_arithmetic_proof_chains(tmp_path):
    driver, errors = compile_source(tmp_path, (ROOT / "Arithmetic.ae").read_text())
    assert not errors, errors
    assert not driver.has_synth()


@pytest.mark.parametrize("name", ["false_step", "false_goal", "nonterminating", "circular_contract"])
def test_invalid_proofs_are_rejected(tmp_path, name):
    _, errors = compile_source(tmp_path, (ROOT / "negative" / f"{name}.ae").read_text())
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors


def test_incomplete_pattern_is_not_a_completed_proof(tmp_path):
    driver, errors = compile_source(tmp_path, (ROOT / "negative" / "incomplete.ae").read_text())
    # Aeon uses missing match branches as synthesis holes. A successful parse
    # alone must never be presented as a verified, complete proof.
    assert errors or driver.has_synth()


def test_invalid_machine_implementation_is_rejected(tmp_path):
    source = (ROOT / "Paper.ae").read_text().split("# First-order specialization")[0]
    assert "(n + m) ss" in source
    source = source.replace("(n + m) ss", "(n - m) ss")
    _, errors = compile_source(tmp_path, source)
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors


def test_induction_hypothesis_is_required(tmp_path):
    source = (ROOT / "Paper.ae").read_text().split("theorem rightIdP")[0]
    source += "def unsupported (xs:(List Int)) : {p:Unit | append xs emptyList = xs} := unit;"
    _, errors = compile_source(tmp_path, source)
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors


@pytest.mark.parametrize("kind,value", [("Int", "7"), ("Bool", "true"), ("String", '"aeon"')])
def test_polymorphic_combinators_return_the_value(tmp_path, kind, value):
    source = f"""import ProofCombinators;
    def main (_:Int) : {kind} := ({value} ==. {value}) ? ProofCombinators.trivial;
    """
    driver, errors = compile_source(tmp_path, source, no_main=False)
    assert not errors, errors
    assert driver.run() == {"Int": 7, "Bool": True, "String": "aeon"}[kind]


def test_hole_syntax_still_parses(tmp_path):
    driver, errors = compile_source(tmp_path, "def pending (x:Int) : Int := ?result;")
    assert not errors, errors
    assert driver.has_synth()


def test_manifest_covers_every_port_and_negative_fixture():
    manifest = json.loads((ROOT / "manifest.json").read_text())
    assert len(manifest["revision"]) == 40
    assert set(manifest["files"]) == {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.ae")}
    source = (ROOT / "Paper.ae").read_text()
    for item in manifest["examples"]:
        assert item["source"] and item["symbols"] and item["adaptation"]
        for symbol in item["aeon"]:
            assert any(f"{keyword} {symbol} " in source for keyword in ("def", "theorem"))
    assert {item["section"] for item in manifest["examples"]} >= {"2", "3", "4", "5", "6"}


def test_examples_use_standard_containers():
    source = (ROOT / "Paper.ae").read_text()
    assert "import List;" in source and "import Maybe;" in source
    assert "inductive List" not in source and "inductive Result" not in source


def test_standard_lists_at_two_element_types(tmp_path):
    source = """import List;
    import Maybe;
    import ProofCombinators;
    def integers (xs:(List Int)) : {p:Unit | xs = xs} :=
      match xs with | nil => xs ==. List.nil{Int} *** QED | cons h t => xs ==. List.cons h t *** QED;
    def booleans (xs:(List Bool)) : {p:Unit | xs = xs} :=
      match xs with | nil => List.nil{Bool} ==. xs *** QED | cons h t => List.cons h t ==. xs *** QED;
    def nested (xs:(List Bool)) : Unit :=
      Maybe.just xs ==. Maybe.just xs *** QED;
    def main (_:Int) : Int :=
      let i := integers [1, 2] in let b := booleans [true, false] in
      let n := nested [true] in List.length [1, 2, 3];
    """
    driver, errors = compile_source(tmp_path, source, no_main=False)
    assert not errors, errors
    assert not driver.has_synth()
    assert driver.run() == 3


def test_standard_list_constructor_cannot_prove_wrong_element(tmp_path):
    source = """import List;
    import ProofCombinators;
    def falseHead (xs:(List Bool)) : Unit :=
      match xs with | nil => unit | cons h t => List.cons true t ==. List.cons false t *** QED;

    """
    _, errors = compile_source(tmp_path, source)
    assert any(isinstance(e, LiquidTypeCheckingFailedRelation) for e in errors), errors
