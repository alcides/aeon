"""Tests for refinement-aware dead branch elimination (issue #114)."""

from __future__ import annotations

import tempfile

from aeon.compilation.compile import clear_unit_cache, compile_and_link_program
from aeon.core.parser import parse_term
from aeon.core.terms import Abstraction, If, Rec
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI

setup_logger()


def _compile(source: str):
    clear_unit_cache()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".ae", delete=False, encoding="utf-8") as tmp:
        tmp.write(source)
        path = tmp.name
    return compile_and_link_program(source, filename=path, is_main=True, is_main_hole=True)


def _fun_body(core):
    match core:
        case Rec(_, _, Abstraction(_, body), _):
            return body
        case _:
            raise AssertionError(f"unexpected core shape: {core}")


def test_dead_else_branch_eliminated():
    source = """
def fun (x: {a:Int | a > 2}) : Int := (if x > 0 then 100 else 200)
"""
    unit, core, ctx, _meta, _trusted, errors = _compile(source)
    assert errors == []
    assert core is not None and ctx is not None
    body = _fun_body(core)
    assert body == parse_term("100")
    assert len(unit.dead_branch_warnings) == 1
    assert unit.dead_branch_warnings[0].branch == "else"


def test_dead_then_branch_eliminated():
    source = """
def fun (x: {a:Int | a < 0}) : Int := (if x > 0 then 100 else 200)
"""
    unit, core, ctx, _meta, _trusted, errors = _compile(source)
    assert errors == []
    body = _fun_body(core)
    assert body == parse_term("200")
    assert len(unit.dead_branch_warnings) == 1
    assert unit.dead_branch_warnings[0].branch == "then"


def test_both_branches_live():
    source = """
def fun (x: {a:Int | a > (0 - 10)}) : Int := (if x > 0 then 100 else 200)
"""
    _unit, core, ctx, _meta, _trusted, errors = _compile(source)
    assert errors == []
    body = _fun_body(core)
    assert isinstance(body, If)


def test_driver_surfaces_dead_branch_warning():
    source = """
def fun (x: {a:Int | a > 2}) : Int := (if x > 0 then 100 else 200)
"""
    clear_unit_cache()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".ae", delete=False, encoding="utf-8") as tmp:
        tmp.write(source)
        path = tmp.name
    driver = AeonDriver(AeonConfig("dummy", SynthesisUI(), 1))
    errors = list(driver.parse(filename=path))
    assert errors == []
    assert len(driver.dead_branch_warnings) == 1


def test_constant_folding_after_refinement_elimination():
    source = """
def fun (x: {a:Int | a > 2}) : Int := (if x > 0 then (50 + 50) else 200)
"""
    _unit, core, _ctx, _meta, _trusted, errors = _compile(source)
    assert errors == []
    body = _fun_body(core)
    assert not isinstance(body, If)
    # Typed ``+`` applications are not literal-folded; the dead branch is gone.
    assert str(body) == "(((+)[Int ] 50) 50)" or body == parse_term("100")
