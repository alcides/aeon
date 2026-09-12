"""Dependent Horn assignments must preserve, but never strengthen, refinements."""

from pathlib import Path

import pytest

from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile


@pytest.mark.parametrize("bound,accepted", [(0, True), (10, False)])
def test_tournament_refinement(bound: int, accepted: bool):
    source = (Path(__file__).resolve().parents[1] / "examples/verification/horn_tournament.ae").read_text()
    source = source.replace("winner > 0", f"winner > {bound}")
    assert check_compile(source, st_top) is accepted
