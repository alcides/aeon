"""Pinned PLDI16 provenance and regressions for restored Synquid contracts."""

import hashlib
import json
from pathlib import Path
import re

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


ROOT = Path(__file__).resolve().parents[1] / "examples/benchmarks/synquid"
MANIFEST = json.loads((ROOT / "manifest.json").read_text())
CASES = MANIFEST["benchmarks"]


def driver_for(source, *, run=False):
    driver = AeonDriver(AeonConfig("synquid", SilentSynthesisUI(), 5, no_main=not run))
    errors = list(driver.parse(aeon_code=source))
    return driver, errors


def source(name):
    return (ROOT / f"{name}.ae").read_text()


def test_inventory_is_complete_and_sources_are_unchanged():
    assert {case["aeon_file"] for case in CASES} == {p.name for p in ROOT.glob("*.ae")}
    assert len(CASES) == 64
    assert {case["upstream_file"] for case in CASES} == {f"upstream/{p.name}" for p in (ROOT / "upstream").glob("*.sq")}
    for case in CASES:
        original = (ROOT / case["upstream_file"]).read_bytes()
        assert hashlib.sha256(original).hexdigest() == case["sha256"]
        goals = re.findall(r"^([a-zA-Z][\w']*)\s*=\s*\?\?", original.decode(), re.M)
        assert goals == case["upstream_goals"]
        if case["status"] != "contract-faithful":
            assert case["gaps"], case["id"]
        else:
            assert not case["gaps"], case["id"]


@pytest.mark.parametrize("case", CASES, ids=lambda case: case["id"])
def test_benchmark_compiles_and_retains_synthesis_goals(case):
    driver = AeonDriver(AeonConfig("synquid", SilentSynthesisUI(), 5, no_main=True))
    assert not list(driver.parse(filename=str(ROOT / case["aeon_file"])))
    assert driver.has_synth()
    if case["status"] in {"contract-faithful", "partial"}:
        assert {name.name for name, _ in driver.incomplete_functions} == set(case["upstream_goals"])
        # No existing library solution to the target may leak into its grammar.
        assert "open List" not in source(case["id"])


FOLD_BODY = "match ys with | nil => seed | cons x xs => f xs x (foldr{a}{b}{|p|} f seed xs)"


@pytest.mark.parametrize("rename", [False, True], ids=["same-binder", "alpha-renamed-binder"])
def test_original_dependent_fold_checks_and_runs(rename):
    program = source("List-Foldr").replace("?hole", FOLD_BODY)
    if rename:
        # The schema and implementation need not use the same predicate binder.
        program = program.replace("Λ <p:(List a) -> b -> Bool>", "Λ <q:(List a) -> b -> Bool>")
        program = program.replace("foldr{a}{b}{|p|}", "foldr{a}{b}{|q|}")
    program += """
    def main (u:Int) : {v:Int | v = 2} :=
        foldr{Int}{Int}{|fun xs => fun acc => acc = List.len xs|}
            (fun xs => fun x => fun acc => acc + 1) 0 (List.cons 4 (List.cons 8 List.nil));
    """
    driver, errors = driver_for(program, run=True)
    assert not errors
    assert driver.run() == 2


@pytest.mark.parametrize("body", ["seed", FOLD_BODY.replace("f seed xs", "f seed ys")])
def test_fold_rejects_ignored_input_and_nondecreasing_recursion(body):
    assert driver_for(source("List-Foldr").replace("?hole", body))[1]


# The upstream solution uses error in the impossible nil branch. An inert native
# value closes that branch for Aeon's eager recursor; the wrong reachable branch
# below must still fail verification. This is only a test witness.
ITH_BODY = 'match xs with | nil => (native "None" :a) | cons x tail => if i = 0 then x else ith{a}{|fun j => fun y => p (j + 1) y|} tail (i - 1)'


def test_indexed_list_shifts_the_predicate_and_ith_returns_the_right_value():
    program = source("List-Ith").replace("?hole", ITH_BODY)
    program += """
    def input : {xs:(List Int){|fun i => fun v => v = i + 10|} | List.len xs = 2} :=
        List.cons{Int}{|fun i => fun v => v = i + 10|} 10
            (List.cons{Int}{|fun i => fun v => v = i + 11|} 11
                (List.nil{Int}{|fun i => fun v => v = i + 12|}));
    def main (u:Int) : {v:Int | v = 11} :=
        ith{Int}{|fun i => fun v => v = i + 10|} input 1;
    """
    driver, errors = driver_for(program, run=True)
    assert not errors
    assert driver.run() == 11
    assert driver_for(program.replace("else ith{a}{|fun j => fun y => p (j + 1) y|} tail (i - 1)", "else x"), run=True)[
        1
    ]
    assert driver_for(program.replace("|} 11\n", "|} 12\n"), run=True)[1]


def test_reverse_identity_no_longer_satisfies_the_contract():
    assert driver_for(source("List-Reverse").replace("?hole", "xs"))[1]
    body = """match xs with
        | nil => List.nil{a}{|fun u => fun v => p v u|}
        | cons head tail => snoc{a}{|fun u => fun v => p v u|} head
            (reverse{{v:a | p head v}}{|p|} tail)"""
    assert not driver_for(source("List-Reverse").replace("?hole", body))[1]


@pytest.mark.parametrize("value,valid", [("2", True), ("1", False)])
def test_unique_range_type_rejects_duplicate_elements(value, valid):
    # Use the actual benchmark datatype and target contract, instantiate size=2.
    program = source("UniqueList-Range").split("def range")[0]
    program += f"""
    def witness : {{xs:(PList {{v:Int | 1 <= v && v <= 3}}){{|fun x => fun y => x != y|}} | PList.len xs = 2}} :=
        PList.cons{{{{v:Int | 1 <= v && v <= 3}}}}{{|fun x => fun y => x != y|}} 1
            (PList.cons{{{{v:Int | 1 <= v && v <= 3 && v != 1}}}}{{|fun x => fun y => x != y|}} {value}
                (PList.nil{{{{v:Int | 1 <= v && v <= 3 && v != 1 && v != {value}}}}}{{|fun x => fun y => x != y|}}));
    """
    assert (not driver_for(program)[1]) == valid


def test_balanced_tree_requires_equal_child_heights():
    datatype = source("Tree-BalancedReplicate").split("def zero")[0]
    balanced = "def tree : (BalTree Int) := BalTree.node 1 BalTree.empty BalTree.empty;"
    assert not driver_for(datatype + balanced)[1]
    unbalanced = (
        "def tree : (BalTree Int) := BalTree.node 1 (BalTree.node 2 BalTree.empty BalTree.empty) BalTree.empty;"
    )
    assert driver_for(datatype + unbalanced)[1]


def test_address_book_classification_is_enforced():
    program = source("AddressBook-Make").split("def mkAddressBook")[0]
    program += """
    def book (business:(List {v:Address | !(Address.isPriv v)}))
             (personal:(List {v:Address | Address.isPriv v})) : AddressBook :=
        AddressBook.addressBook business personal;
    """
    assert not driver_for(program)[1]
    assert driver_for(
        program.replace("AddressBook.addressBook business personal", "AddressBook.addressBook personal business")
    )[1]


def test_evaluator_is_a_semantics_preserving_ast_translation():
    body = """match x with
        | zero => PAST.intNode 0
        | one => PAST.intNode 1
        | two => PAST.intNode 2
        | plusNode l r => PAST.opNode 0 (transform l) (transform r)
        | minusNode l r => PAST.opNode 1 (transform l) (transform r)
        | productNode l r => PAST.opNode 2 (transform l) (transform r)"""
    program = source("Evaluator").replace("?hole", body)
    assert not driver_for(program)[1]
    assert driver_for(program.replace("PAST.opNode 1", "PAST.opNode 0"))[1]
