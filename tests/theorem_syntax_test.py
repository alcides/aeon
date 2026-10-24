"""Theorem syntax produces checked, complete proofs during compilation."""

import pytest

from aeon.compilation.proofs import IncompleteTheoremError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_source(tmp_path, source):
    path = tmp_path / "theorems.ae"
    path.write_text(source)
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True, check_only=True))
    return driver, list(driver.parse(filename=str(path), aeon_code=source))


def test_arithmetic_have_calc_and_exact(tmp_path):
    driver, errors = compile_source(
        tmp_path,
        """
theorem comm (a:Int) (b:Int): a + b = b + a := by
  smt

theorem zero (x:Int): x + 0 = x := by
  have h : x + 0 = 0 + x := by
    exact comm x 0
  calc
    x + 0 = 0 + x := by exact h
    _ = x := by smt
""",
    )
    assert not errors, errors
    assert not driver.has_synth()


@pytest.mark.parametrize(
    "source",
    [
        "theorem false_constant : false := by smt;",
        "theorem false_function (x:Int) : x = x + 1 := by smt;",
        "theorem bad_step (x:Int):x = x := calc (x = x + 1 := by smt; _ = x := by smt);",
        "theorem bad_join : 0 = 1 := calc (0 = 0 := by smt; 1 = 1 := by smt);",
    ],
)
def test_false_proofs_rejected(tmp_path, source):
    _, errors = compile_source(tmp_path, source)
    assert errors


@pytest.mark.parametrize("body", ["?todo", "by assumption", "match x with |yes => unit"])
def test_unfinished_theorem_is_compilation_error(tmp_path, body):
    _, errors = compile_source(
        tmp_path, f"inductive Choice |yes:Choice |no:Choice\ntheorem unfinished (x:Choice):true := {body};"
    )
    assert any(isinstance(e, IncompleteTheoremError) for e in errors), errors


def test_synthesis_tactic_runs_during_check_only(tmp_path):
    driver, errors = compile_source(tmp_path, "theorem done (h:{p:Unit | true}):true := by assumption;")
    assert not errors, errors
    assert not driver.has_synth()


def test_cases_and_rewrite(tmp_path):
    _, errors = compile_source(
        tmp_path,
        """
inductive Choice |yes:Choice |no:Choice
theorem choice (x:Choice): x = x := by
  cases x with
  | yes => smt
  | no => smt

theorem use (x:Int) (h:{p:Unit | x = 0}): x + 1 = 1 := by
  rw [h]
  smt
""",
    )
    assert not errors, errors


def test_list_induction(tmp_path):
    source = """import List;
def empty : {v:(List Int) | v = List.nil && List.structuralRank v = 0} := List.nil;
def append (xs:(List Int)) (ys:(List Int)) : {r:(List Int) |
 (List.structuralRank xs = 0 --> r = ys) &&
 (List.structuralRank xs > 0 --> r = List.cons (List.first xs) (append (List.rest xs) ys))}
 decreasing_by [List.structuralRank xs] :=
 match xs with |nil => ys |cons h t => List.cons h (append t ys);
theorem append_nil (xs:(List Int)): append xs empty = xs := by
  induction xs with
  | nil => smt
  | cons x tail ih => simp [ih]
"""
    driver, errors = compile_source(tmp_path, source)
    assert not errors, errors
    assert not driver.has_synth()
    _, errors = compile_source(tmp_path, source.replace("simp [ih]", "exact ?unfinished"))
    assert any(isinstance(e, IncompleteTheoremError) for e in errors), errors


def test_non_decreasing_recursive_theorem_rejected(tmp_path):
    _, errors = compile_source(tmp_path, "theorem loop (n:Int):false decreasing_by [n] := by exact loop n;")
    assert errors


def test_library_theorem_is_checked_and_exported(tmp_path):
    from aeon.compilation.compile import compile_program

    unit, errors = compile_program(
        "theorem done (h:{p:Unit | true}):true := by assumption;",
        filename=str(tmp_path / "ProofLibrary.ae"),
        is_main=False,
        use_cache=False,
    )
    assert not errors, errors
    assert any("done" in str(name) for name in unit.exports)
    _, errors = compile_program(
        "theorem wrong (n:Int):n = n + 1 := by smt;",
        filename=str(tmp_path / "BadProofLibrary.ae"),
        is_main=False,
        use_cache=False,
    )
    assert errors


def test_tactic_inside_have_runs_at_compile_time(tmp_path):
    driver, errors = compile_source(
        tmp_path,
        """
theorem done (h:{p:Unit | true}):true := by
  have inner : true := by assumption
  exact inner
""",
    )
    assert not errors, errors
    assert not driver.has_synth()


def test_theorem_cannot_depend_on_unfinished_definition(tmp_path):
    _, errors = compile_source(
        tmp_path,
        """
def unfinished (x:Int):{p:Unit | x = 0} := ?pending;
theorem wrong : 1 = 0 := by exact unfinished 1;
""",
    )
    assert any(isinstance(e, IncompleteTheoremError) for e in errors), errors


def test_namespaced_theorem_must_be_complete(tmp_path):
    _, errors = compile_source(tmp_path, "namespace Proof\ntheorem unfinished : true := ?todo;\nend")
    assert any(isinstance(e, IncompleteTheoremError) for e in errors), errors


def test_layout_comments_and_multiline_expression(tmp_path):
    _, errors = compile_source(
        tmp_path,
        """
theorem identity (n:Int):n = n := by
  smt # first proof

theorem use (n:Int):n = n := by # outer block
  have h : n = n := by # inner block
    exact identity
      n
  exact h
""",
    )
    assert not errors, errors


def test_theorem_statement_cannot_be_synthesized_implicitly(tmp_path):
    _, errors = compile_source(tmp_path, "theorem unspecified : ?statement := by smt;")
    assert any(isinstance(e, IncompleteTheoremError) for e in errors), errors


def test_calc_missing_start_has_diagnostic(tmp_path):
    from aeon.errors import ProofElaborationError

    _, errors = compile_source(tmp_path, "theorem bad : true := calc (_ = 0 := by smt);")
    assert any(isinstance(e, ProofElaborationError) for e in errors), errors


def test_polymorphic_theorem(tmp_path):
    _, errors = compile_source(tmp_path, "theorem reflexive (x:a):x = x := by smt;")
    assert not errors, errors


def test_standalone_induction_example(tmp_path):
    from pathlib import Path

    source = (Path(__file__).resolve().parents[1] / "examples/proofs/Induction.ae").read_text()
    driver, errors = compile_source(tmp_path, source)
    assert not errors, errors
    assert not driver.has_synth()


def test_induction_example_can_be_exported_as_a_library(tmp_path):
    from pathlib import Path
    from aeon.compilation.compile import compile_program

    source = (Path(__file__).resolve().parents[1] / "examples/proofs/Induction.ae").read_text()
    unit, errors = compile_program(source, filename=str(tmp_path / "ProofLibrary.ae"), is_main=False, use_cache=False)
    assert not errors, errors
    assert "append_nil" in unit.exports
