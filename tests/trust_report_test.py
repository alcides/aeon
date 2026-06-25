"""The ``--trust-report`` tool (issue #442).

A program's verified guarantees rest on assumptions the type checker does
*not* check: ``axiom`` declarations and ``native`` bindings whose type
carries a refinement. These tests pin down that the report collects exactly
those, distinguishes axioms from natives, narrows to a function's transitive
dependencies, and excludes verified definitions and unrefined natives.
"""

from __future__ import annotations

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import AbstractionType, RefinedType, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.facade.trust import compute_trust_report, has_nontrivial_refinement, render_type
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


def _driver(source: str) -> AeonDriver:
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=True,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert not errors, errors
    return driver


def _report(source: str, for_func: str | None = None):
    driver = _driver(source)
    return compute_trust_report(driver.core, filename="<test>", for_func=for_func)


def test_native_refined_binding_is_trusted():
    src = """
    def safe_abs (i:Int) : {v:Int | v >= 0} := native "abs(i)"
    def main (a:Int) : Int := safe_abs a ;
    """
    report = _report(src)
    natives = {i.display for i in report.natives}
    assert "safe_abs" in natives
    item = next(i for i in report.natives if i.display == "safe_abs")
    assert item.native_code == "abs(i)"
    assert item.kind == "native"


def test_unrefined_native_is_not_trusted():
    # A native over plain base types asserts no refinement → excluded.
    src = """
    def raw (i:Int) : Int := native "i"
    def main (a:Int) : Int := raw a ;
    """
    report = _report(src)
    assert all(i.display != "raw" for i in report.natives)


def test_verified_definition_is_not_trusted():
    # `double` has a refinement but is *verified* (not native) → excluded.
    src = """
    def double (x:Int) : {v:Int | v = x + x} := x + x
    def main (a:Int) : Int := double a ;
    """
    report = _report(src)
    assert all(i.display != "double" for i in report.items)


def test_axiom_is_reported_and_classified():
    src = """
    def p : (x:Int) -> Bool := uninterpreted
    axiom assume_p : (x:Int) -> {u:Unit | p x = true} ;
    def main (a:Int) : Int :=
        let inst := assume_p a in a ;
    """
    report = _report(src)
    axioms = {i.display for i in report.axioms}
    assert "assume_p" in axioms


def test_trust_for_narrows_to_dependencies():
    src = """
    def safe_abs (i:Int) : {v:Int | v >= 0} := native "abs(i)"
    def helper (i:Int) : {v:Int | v >= 1} := native "abs(i) + 1"
    def uses_abs (x:Int) : Int := safe_abs x
    def main (a:Int) : Int := uses_abs a ;
    """
    # Reachable from `uses_abs`: only safe_abs, not helper.
    scoped = {i.display for i in _report(src, for_func="uses_abs").items}
    assert "safe_abs" in scoped
    assert "helper" not in scoped
    # Whole program: both.
    whole = {i.display for i in _report(src).items}
    assert {"safe_abs", "helper"} <= whole


def test_module_prefix_rendered_with_dot():
    src = """
    open Math
    def main (a:Int) : Int := Math.abs a ;
    """
    report = _report(src, for_func="main")
    displays = {i.display for i in report.items}
    assert "Math.abs" in displays


def test_has_nontrivial_refinement_helper():
    refined = RefinedType(Name("v", 0), t_int, LiquidLiteralBool(False))
    assert has_nontrivial_refinement(refined)
    assert not has_nontrivial_refinement(t_int)
    assert has_nontrivial_refinement(AbstractionType(Name("i", 0), t_int, refined))
    assert not has_nontrivial_refinement(AbstractionType(Name("i", 0), t_int, t_int))


def test_render_type_strips_binder_ids():
    # A binder with an id renders with superscripts in str(); the report strips them.
    refined = RefinedType(Name("v", 136), t_int, LiquidLiteralBool(False))
    assert "¹³⁶" in str(refined)
    rendered = render_type(refined)
    assert not any(ch in rendered for ch in "⁰¹²³⁴⁵⁶⁷⁸⁹")
    assert "Int" in rendered
