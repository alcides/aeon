"""Tests for SMT reflection of inductive types as Z3 Datatypes."""

from __future__ import annotations

from z3 import DatatypeSortRef

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.types import TypeConstructor, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name
from aeon.verification.constructor_registry import clear_constructor_registry, get_constructor_order
from aeon.verification.smt import get_sort, smt_valid, translate_liq
from aeon.verification.smt_datatypes import (
    clear_datatype_cache,
    constructors_for_env,
    lookup_constructor,
)
from aeon.verification.vcs import Implication, LiquidConstraint


def _load_list() -> TypeConstructor:
    """Import ``List`` so the constructor registry is populated."""
    clear_constructor_registry()
    clear_datatype_cache()
    cfg = AeonConfig(synthesizer="smt", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    d = AeonDriver(cfg)
    assert d.parse(aeon_code="import List\ndef main (x:Int) : Int := 0;", filename="<t>") == []
    assert get_constructor_order("List") is not None
    # Binder ids on ``List`` must not matter: inductive SMT sorts are keyed by
    # logical name (``List_Int``), matching the constructor registry.
    return TypeConstructor(Name("List", 0), [t_int])


def test_list_int_is_z3_datatype():
    list_int = _load_list()
    sort = get_sort(list_int)
    assert isinstance(sort, DatatypeSortRef)
    assert str(sort) == "List_Int"


def test_list_constructors_are_reflected():
    list_int = _load_list()
    get_sort(list_int)
    nil = lookup_constructor("List_nil")
    cons = lookup_constructor("List_cons")
    assert nil is not None
    assert cons is not None
    env = constructors_for_env()
    assert "List_nil" in env and "List_cons" in env


def test_list_nil_resolves_in_liquid_translation():
    """The Contata failure mode: ``List_nil`` mentioned without a binder id."""
    list_int = _load_list()
    get_sort(list_int)
    env = constructors_for_env()
    term = translate_liq(LiquidVar(Name("List_nil", 1054)), env)
    assert term is not None


def test_list_cons_app_in_liquid_translation():
    list_int = _load_list()
    get_sort(list_int)
    env = constructors_for_env()
    term = LiquidApp(
        Name("List_cons", 0),
        [LiquidLiteralInt(3), LiquidVar(Name("List_nil", 0))],
    )
    z3t = translate_liq(term, env)
    assert z3t is not None


def test_list_nil_equals_itself_valid():
    list_int = _load_list()
    get_sort(list_int)
    # Same logical type with a *different* binder id still shares ``List_Int``.
    list_int_other_id = TypeConstructor(Name("List", 999), [t_int])
    name_x = Name("x", 1)
    constraint = Implication(
        name_x,
        list_int_other_id,
        LiquidApp(Name("==", 0), [LiquidVar(name_x), LiquidVar(Name("List_nil", 0))]),
        LiquidConstraint(
            LiquidApp(Name("==", 0), [LiquidVar(name_x), LiquidVar(Name("List_nil", 0))]),
        ),
    )
    assert smt_valid(constraint)


def test_list_cons_nil_roundtrip_typechecks():
    """End-to-end: programs mentioning ``nil``/``cons`` typecheck with ADT SMT."""
    clear_constructor_registry()
    clear_datatype_cache()
    cfg = AeonConfig(synthesizer="smt", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    d = AeonDriver(cfg)
    errs = d.parse(
        aeon_code="""
open List
def main (x:Int) : Int :=
    if empty (cons 1 nil) then 1 else 0;
""",
        filename="<list_adt>",
    )
    assert errs == []


def test_list_size_measure_is_recfunction():
    """LH measures become Z3 RecFunctions (size nil = 0, size (cons …) = 1+…)."""
    from z3 import is_func_decl, simplify

    from aeon.verification.smt_datatypes import lookup_measure

    list_int = _load_list()
    get_sort(list_int)
    sz = lookup_measure("List_size")
    assert sz is not None
    assert is_func_decl(sz)
    nil = lookup_constructor("List_nil")
    cons = lookup_constructor("List_cons")
    assert simplify(sz(nil)).as_long() == 0
    assert simplify(sz(cons(3, nil))).as_long() == 1
    assert simplify(sz(cons(1, cons(2, nil)))).as_long() == 2


def test_list_size_nil_entailment():
    """``size nil == 0`` is SMT-valid via the recursive measure definition."""
    list_int = _load_list()
    get_sort(list_int)
    constraint = LiquidConstraint(
        LiquidApp(
            Name("==", 0),
            [
                LiquidApp(Name("List_size", 0), [LiquidVar(Name("List_nil", 0))]),
                LiquidLiteralInt(0),
            ],
        ),
    )
    assert smt_valid(constraint)


def test_list_size_cons_entailment():
    """``size (cons 3 nil) == 1`` discharges structurally."""
    list_int = _load_list()
    get_sort(list_int)
    cons_app = LiquidApp(
        Name("List_cons", 0),
        [LiquidLiteralInt(3), LiquidVar(Name("List_nil", 0))],
    )
    constraint = LiquidConstraint(
        LiquidApp(
            Name("==", 0),
            [
                LiquidApp(Name("List_size", 0), [cons_app]),
                LiquidLiteralInt(1),
            ],
        ),
    )
    assert smt_valid(constraint)
