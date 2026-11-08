"""Tests for SMT reflection of inductive types as Z3 Datatypes."""

from __future__ import annotations

from collections.abc import Iterator
import pytest
from z3 import DatatypeSortRef

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidLiteralUnit, LiquidVar
from aeon.core.types import TypeConstructor, t_int, t_unit
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


@pytest.fixture
def list_int() -> Iterator[TypeConstructor]:
    """Query the imported datatype in the session which owns its declarations."""
    cfg = AeonConfig(synthesizer="smt", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    d = AeonDriver(cfg)
    assert d.parse(aeon_code="import List\ndef main (x:Int) : Int := 0;", filename="<t>") == []
    with d.session.activate():
        assert get_constructor_order("List") is not None
        # Binder ids on ``List`` must not matter: inductive SMT sorts are keyed
        # by logical name (``List_Int``), matching the constructor registry.
        yield TypeConstructor(Name("List", 0), [t_int])


def test_list_int_is_z3_datatype(list_int):
    sort = get_sort(list_int)
    assert isinstance(sort, DatatypeSortRef)
    assert str(sort) == "List_Int"


def test_list_constructors_are_reflected(list_int):
    get_sort(list_int)
    nil = lookup_constructor("List_nil")
    cons = lookup_constructor("List_cons")
    assert nil is not None
    assert cons is not None
    env = constructors_for_env()
    assert "List_nil" in env and "List_cons" in env


def test_list_nil_resolves_in_liquid_translation(list_int):
    """The Contata failure mode: ``List_nil`` mentioned without a binder id."""
    get_sort(list_int)
    env = constructors_for_env()
    term = translate_liq(LiquidVar(Name("List_nil", 1054)), env)
    assert term is not None


def test_list_cons_app_in_liquid_translation(list_int):
    get_sort(list_int)
    env = constructors_for_env()
    term = LiquidApp(
        Name("List_cons", 0),
        [LiquidLiteralInt(3), LiquidVar(Name("List_nil", 0))],
    )
    z3t = translate_liq(term, env)
    assert z3t is not None


def test_list_nil_equals_itself_valid(list_int):
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


@pytest.mark.parametrize("base,value", [(t_unit, LiquidLiteralUnit()), (t_int, LiquidLiteralInt(7))])
def test_shadowed_constructor_uses_declared_sort(list_int, base, value):
    get_sort(list_int)
    # Synthesis excludes constructors by shadowing them with Unit bindings.
    # A local binding must not resolve to the same-named datatype constant.
    shadow = Name("List_nil", 9509)

    def obligation(result):
        return Implication(
            shadow,
            base,
            LiquidApp(Name("==", 0), [LiquidVar(shadow), value]),
            LiquidConstraint(LiquidApp(Name("==", 0), [LiquidLiteralInt(1), LiquidLiteralInt(result)])),
        )

    assert smt_valid(obligation(1))
    assert not smt_valid(obligation(2))


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


def test_list_size_measure_is_recfunction(list_int):
    """LH measures become Z3 RecFunctions (size nil = 0, size (cons …) = 1+…)."""
    from z3 import is_func_decl, simplify

    from aeon.verification.smt_datatypes import lookup_measure

    get_sort(list_int)
    sz = lookup_measure("List_size")
    assert sz is not None
    assert lookup_measure("size") is None
    assert is_func_decl(sz)
    nil = lookup_constructor("List_nil")
    cons = lookup_constructor("List_cons")
    assert simplify(sz(nil)).as_long() == 0
    assert simplify(sz(cons(3, nil))).as_long() == 1
    assert simplify(sz(cons(1, cons(2, nil)))).as_long() == 2


def test_list_size_nil_entailment(list_int):
    """``size nil == 0`` is SMT-valid via the recursive measure definition."""
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


def test_list_size_cons_entailment(list_int):
    """``size (cons 3 nil) == 1`` discharges structurally."""
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


def test_polymorphic_measure_specialization_uses_matching_datatype_sort(list_int):
    from aeon.core.types import TypeVar, AbstractionType
    from aeon.verification.sub import lower_constraint_type
    from aeon.verification.vcs import UninterpretedFunctionDeclaration
    from aeon.core.liquid import LiquidLiteralBool

    element = TypeVar(Name("a", 9501))
    datatype = TypeConstructor(list_int.name, [element])
    xs, hd, size = Name("xs", 9502), Name("hd", 9503), Name("List_size", 9504)
    cons = LiquidApp(Name("List_cons", 9505), [LiquidVar(hd), LiquidVar(Name("List_nil", 9506))])
    signature = lower_constraint_type(AbstractionType(Name("list", 9507), datatype, t_int))

    def obligation(length):
        return UninterpretedFunctionDeclaration(
            size,
            signature,
            Implication(
                hd,
                element,
                LiquidLiteralBool(True),
                Implication(
                    xs,
                    datatype,
                    LiquidApp(Name("==", 0), [LiquidVar(xs), cons]),
                    LiquidConstraint(
                        LiquidApp(Name("==", 0), [LiquidApp(size, [LiquidVar(xs)]), LiquidLiteralInt(length)])
                    ),
                ),
            ),
        )

    assert smt_valid(obligation(1))
    assert not smt_valid(obligation(2))


@pytest.mark.parametrize("measure", ["size", "cardinality"])
def test_structural_measure_requires_matching_constructor_equations(measure):
    from z3 import simplify

    from aeon.verification.smt_datatypes import lookup_measure

    program = f"""
    inductive Counter
    | zero : {{v:Counter | {measure} v = 0}}
    | next (tail:Counter) : {{v:Counter | 1 + {measure} tail = {measure} v}}
    + {measure} (v:Counter) : Int
    """
    driver = AeonDriver(AeonConfig("smt", SilentSynthesisUI(), 0, no_main=True))
    assert not list(driver.parse(aeon_code=program))
    with driver.session.activate():
        get_sort(TypeConstructor(Name("Counter", 0)))
        size = lookup_measure(f"Counter_{measure}")
        assert size is not None
        zero, next_ = lookup_constructor("Counter_zero"), lookup_constructor("Counter_next")
        assert simplify(size(next_(next_(zero)))).as_long() == 2


@pytest.mark.parametrize("leaf,increment", [(1, 1), (0, 2)])
def test_size_name_does_not_override_custom_equations(leaf, increment):
    from aeon.verification.smt_datatypes import lookup_measure

    program = f"""
    inductive Counter
    | zero : {{v:Counter | size v = {leaf}}}
    | next (tail:Counter) : {{v:Counter | size v = {increment} + size tail}}
    + size (v:Counter) : Int
    """
    driver = AeonDriver(AeonConfig("smt", SilentSynthesisUI(), 0, no_main=True))
    assert not list(driver.parse(aeon_code=program))
    with driver.session.activate():
        get_sort(TypeConstructor(Name("Counter", 0)))
        assert lookup_measure("Counter_size") is None
    # Contradicting the user's equations used to make arbitrary claims valid.
    assert list(driver.parse(aeon_code=program + "def invalid (u:Int):{v:Int | false} := 0;"))
