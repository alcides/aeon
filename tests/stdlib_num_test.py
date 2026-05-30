"""Tests for the ``Num``/``Ord`` typeclasses shipped in ``libraries/Num.ae``.

These exercise typeclasses *across a module import*: the class and instance
declarations live in the standard library and are pulled into the main
program by ``collect_imported_typeclasses`` so the single ``expand_typeclasses``
pass generates the method projections and registers the instances.
"""

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI

setup_logger()


def _run(source: str):
    cfg = AeonConfig(synthesizer="none", synthesis_ui=SynthesisUI(), synthesis_budget=0)
    driver = AeonDriver(cfg)
    errors = list(driver.parse(aeon_code=source))
    assert not errors, errors
    return driver.run()


def test_num_int_add_sub_mul():
    source = r"""
    open Num

    def main (args : Int) : Int =
        let s : Int = add 3 4 in      # 7
        let d : Int = sub s 2 in      # 5
        mul d 2;                      # 10
    """
    assert _run(source) == 10


def test_num_float_instance_dispatch():
    # Float arithmetic dispatches to ``Num Float``; convert back to Int only
    # via a comparison so the test asserts on an Int result.
    source = r"""
    open Num

    def main (args : Int) : Int =
        let f : Float = add 1.5 2.5 in   # 4.0 via Num Float
        if lt 3.0 f then 0 else 1;       # 3.0 < 4.0 via Ord Float
    """
    assert _run(source) == 0


def test_ord_int_lt_leq():
    source = r"""
    open Num

    def main (args : Int) : Int =
        if lt 1 2 then (if leq 5 5 then 0 else 1) else 2;
    """
    assert _run(source) == 0


def test_ord_default_methods():
    # ``gt`` and ``geq`` are class defaults derived from ``lt``/``leq``; the
    # Int instance provides only ``lt``/``leq``, so this exercises default
    # methods reached through an imported class.
    source = r"""
    open Num

    def main (args : Int) : Int =
        if gt 5 2 then (if geq 5 5 then 0 else 1) else 2;
    """
    assert _run(source) == 0


def test_ord_default_false_branch():
    source = r"""
    open Num

    def main (args : Int) : Int =
        if gt 2 5 then 100 else 200;   # default gt: lt 5 2 == false
    """
    assert _run(source) == 200
