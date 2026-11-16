"""Small, offline Aeon fixtures with independent, exhaustive truth-table oracles.

The tables describe the relation (including witness outputs), not preferred
output labels. Only the .ae files are supplied to synthesis backends.
"""

from itertools import product
import json
from pathlib import Path

from aeon.benchmarks.bounded_boolean.corpus import ROOT, digest
from aeon.benchmarks.bounded_boolean.verilog import Circuit


def circuit(case: dict) -> Circuit:
    inputs = tuple(case["inputs"])
    outputs = tuple(case["outputs"])
    names = inputs + outputs
    table = case["relation_table"]
    if (
        len(names) > 6
        or len(set(names)) != len(names)
        or not outputs
        or len(table) != 2 ** len(names)
        or any(type(v) is not bool for v in table)
        or case["semantics"] not in {"partial", "total"}
    ):
        raise ValueError(f"invalid local truth-table fixture: {case['id']}")
    expression = ["bool", False]
    for bits, holds in zip(product((False, True), repeat=len(names)), table):
        if holds:
            row = ["bool", True]
            for name, value in zip(names, bits):
                literal = ["var", name] if value else ["not", ["var", name]]
                row = ["and", row, literal]
            expression = ["or", expression, row]
    return Circuit(names, ("out",), (("out", expression),), (), outputs, case["semantics"])


def manifest(root: Path = ROOT) -> dict:
    result = json.loads((root / "local/manifest.json").read_text())
    ids = set()
    for case in result["cases"]:
        if case["id"] in ids or case.get("suite") != "local":
            raise ValueError("duplicate or incorrectly classified local fixture")
        ids.add(case["id"])
        circuit(case)
        if digest((root / case["aeon"]).read_bytes()) != case["aeon_sha256"]:
            raise ValueError(f"local source hash mismatch: {case['id']}")
    return result


def oracle_report(root: Path = ROOT) -> dict:
    from aeon.benchmarks.bounded_boolean.checker import exhaustive_status

    entries = []
    for case in manifest(root)["cases"]:
        problem = circuit(case)
        statuses = {str(k): exhaustive_status(problem, k) for k in range(case["oracle_max_bound"] + 1)}
        feasible = [int(k) for k, status in statuses.items() if status == "feasible"]
        minimum = min(feasible) if feasible else None
        expected = case["expected_min_bound"]
        agreement = all(
            status == ("feasible" if expected is not None and int(k) >= expected else "bounded_unsat")
            for k, status in statuses.items()
        )
        entries.append(
            {
                "task": case["id"],
                "aeon_sha256": case["aeon_sha256"],
                "semantics": problem.semantics,
                "statuses": statuses,
                "minimum_bound": minimum,
                "minimum_certified": minimum is not None
                and all(statuses[str(k)] == "bounded_unsat" for k in range(minimum)),
                "agrees_with_fixture": agreement,
            }
        )
    return {
        "suite": "local",
        "method": "exhaustive CNF family and truth-table enumeration; no solver or synthesis calls",
        "manifest_sha256": digest((root / "local/manifest.json").read_bytes()),
        "all_agree": all(e["agrees_with_fixture"] for e in entries),
        "cases": entries,
    }
