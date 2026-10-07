"""Refined ADT match reachability and recursor refinement tests."""

from __future__ import annotations

from aeon.facade.api import UnreachablePatternError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def _parse(source: str):
    driver = AeonDriver(
        AeonConfig(synthesizer="smt", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    )
    return driver.parse(aeon_code=source, filename="<refined-match>")


def test_refined_match_rejects_impossible_nil_branch() -> None:
    errors = _parse(
        """
        import List
        def size_of_nonempty (l:{l:(List Int) | List.size l > 0}) : {n:Int | n > 0} :=
            match l with
            | nil => 0
            | cons hd tl => List.size l;
        """
    )
    assert any(isinstance(error, UnreachablePatternError) for error in errors), errors


def test_unrefined_match_remains_valid() -> None:
    errors = _parse(
        """
        import List
        def possible (l:(List Int)) : Int :=
            match l with
            | nil => 0
            | cons hd tl => 1;
        """
    )
    assert errors == [], errors
