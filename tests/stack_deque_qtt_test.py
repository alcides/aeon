"""QTT / refinement tests for Stack and Deque."""

from __future__ import annotations

from pathlib import Path
import pytest

from aeon.facade.api import (
    LinearityError,
    LinearUnusedError,
    LiquidTypeCheckingFailedRelation,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI


def _parse(source: str):
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    return list(AeonDriver(cfg).parse(aeon_code=source))


def _errors(source: str):
    return _parse(source)


def _linearity_errors(source: str):
    return [e for e in _parse(source) if isinstance(e, LinearityError)]


def _liquid_errors(source: str):
    return [e for e in _parse(source) if isinstance(e, LiquidTypeCheckingFailedRelation)]


MAIN = """
def main (args: Int) : Unit := print "ok";
"""


def test_stack_lifecycle_typechecks():
    src = (
        """
open Stack
def demo (u: Unit) : Int :=
    let 1 s0 := new_stack{Int} u in
    let 1 s1 := push 7 s0 in
    let 1 po := pop s1 in
    with_pop po (fun v => fun s2 =>
        let _ := discard s2 in v);
"""
        + MAIN
    )
    assert _errors(src) == []


def test_stack_pop_empty_is_rejected():
    src = (
        """
open Stack
def bad (u: Unit) : Int :=
    let 1 s0 := new_stack{Int} u in
    let 1 po := pop s0 in
    with_pop po (fun v => fun s1 =>
        let _ := discard s1 in v);
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_stack_leak_is_rejected():
    src = (
        """
open Stack
def leak (u: Unit) : Unit :=
    let 1 s := new_stack{Int} u in
    print "ignored";
"""
        + MAIN
    )
    assert any(isinstance(e, LinearUnusedError) for e in _linearity_errors(src))


def test_stack_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "stack_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []


def test_deque_lifecycle_typechecks():
    src = (
        """
open Deque
def demo (u: Unit) : Int :=
    let 1 d0 := new_deque{Int} u in
    let 1 d1 := push_back 1 d0 in
    let 1 d2 := push_front 0 d1 in
    let 1 po := pop_front d2 in
    with_pop po (fun v => fun d3 =>
        let 1 po2 := pop_back d3 in
        let 1 d4 := pop_deque po2 in
        let _ := discard d4 in v);
"""
        + MAIN
    )
    assert _errors(src) == []


def test_deque_pop_empty_is_rejected():
    src = (
        """
open Deque
def bad (u: Unit) : Int :=
    let 1 d0 := new_deque{Int} u in
    let 1 po := pop_back d0 in
    with_pop po (fun v => fun d1 =>
        let _ := discard d1 in v);
"""
        + MAIN
    )
    assert _liquid_errors(src) != []


def test_deque_example_typechecks():
    example = Path(__file__).parents[1] / "examples" / "imports" / "deque_example.ae"
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    assert AeonDriver(cfg).parse(filename=str(example)) == []


@pytest.mark.parametrize(
    "module,create,push,pop,recover",
    [
        ("Stack", "new_stack", "push", "pop", "pop_stack"),
        ("Deque", "new_deque", "push_back", "pop_back", "pop_deque"),
    ],
)
def test_recovery_token_cannot_duplicate_a_linear_handle(module, create, push, pop, recover):
    source = f"""
    open {module}
    def duplicate(u:Unit):Int :=
        let 1 empty := {create}{{Int}} u in
        let 1 one := {push} 1 empty in
        let 1 two := {push} 2 one in
        let token := {pop} two in
        let 1 a := {recover} token in
        let 1 b := {recover} token in
        let first := {pop} a in
        let second := {pop} b in
        pop_value second;
    """
    assert _linearity_errors(source)


@pytest.mark.parametrize("example", ["stack_example", "deque_example"])
def test_linear_recovery_continuation_runs(example):
    source = (Path(__file__).parents[1] / "examples" / "imports" / f"{example}.ae").read_text()
    source = source[: source.index("def main")] + "def main(u:Int):Int := demo unit;"
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0))
    assert not driver.parse(aeon_code=source)
    assert driver.run() == (2 if example == "stack_example" else 0)
