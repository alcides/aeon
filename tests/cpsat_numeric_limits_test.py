"""Oversized exact domains/coefficients are capability limits, not crashes."""

import subprocess
import sys

import pytest

pytest.importorskip("ortools")

from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer, _Num, _Unsupported


@pytest.mark.parametrize("bound", [10**30, -(10**30)])
def test_unrepresentable_numeric_interval_is_rejected(bound):
    with pytest.raises(_Unsupported, match="64-bit"):
        _Num(bound, 0, bound, bound)


def test_scale_lifting_checks_range_before_constructing_expression():
    from ortools.sat.python import cp_model

    solver = CPSatHoleSynthesizer()
    variable = cp_model.CpModel().new_int_var(0, 10000, "x")
    with pytest.raises(_Unsupported, match="64-bit"):
        solver._lift(_Num(variable, 0, 0, 10000), 6)


def test_comparison_constructs_only_the_requested_operator():
    class EqualityOnly:
        def __eq__(self, other):
            return "equal"

        def __lt__(self, other):
            raise AssertionError("Unrequested comparison")

    assert CPSatHoleSynthesizer._compare("==", EqualityOnly(), 0) == "equal"


@pytest.mark.parametrize(
    "case", ["1rm", "agprice", "arbitrageloops", "bananas", "celsiusfahrenheit", "polygon", "prod0", "twocircles"]
)
def test_reported_hakank_numeric_failures_are_controlled(case):
    pytest.importorskip("ortools")
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "aeon",
            "--no-main",
            "-s",
            "ortools",
            "--budget",
            "1",
            f"examples/synthesis/hakank/catalogue/{case}.ae",
        ],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 2, result.stderr
    assert "Unsupported synthesis goal:" in result.stderr
    assert "64-bit" in result.stderr
    assert "Traceback" not in result.stderr
