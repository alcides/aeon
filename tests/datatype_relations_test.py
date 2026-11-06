"""Datatype predicate arguments survive construction, matching and inference."""

import pytest

from aeon.core.liquid import LiquidApp, LiquidPredicate, LiquidVar
from aeon.core.substitutions import substitution_liquid_in_type
from aeon.core.types import TypeConstructor, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


DUO = """
inductive Duo a forall <r:a -> a -> Bool>
| mk (first:a) (second:{v:a | r first v}) : {d:(Duo a){|r|} | firstValue d = first}
+ firstValue (d:(Duo a)) : a
"""


def driver_for(source):
    driver = AeonDriver(AeonConfig("synquid", SilentSynthesisUI(), 20))
    errors = list(driver.parse(aeon_code=source))
    return driver, errors


@pytest.mark.parametrize("first,second,valid", [(1, 2, True), (2, 1, False), (1, 1, False)])
def test_constructor_enforces_binary_relation(first, second, valid):
    _, errors = driver_for(
        DUO
        + f"""
    def pair : (Duo Int){{|fun x => fun y => x < y|}} := Duo.mk {first} {second};
    """
    )
    assert (not errors) == valid


@pytest.mark.parametrize("body,valid", [("second", True), ("first", False)])
def test_match_recovers_stored_binary_relation(body, valid):
    driver, errors = driver_for(
        DUO
        + f"""
    def second (d:(Duo Int){{|fun x => fun y => x < y|}}) : {{v:Int | v > Duo.firstValue d}} :=
        match d with | mk first second => {body};
    def main (u:Int):Int := second (Duo.mk 1 2);
    """
    )
    assert (not errors) == valid
    if valid:
        assert driver.run() == 2


@pytest.mark.parametrize("source_relation", ["", "{|fun x => fun y => x <= y|}"])
def test_cannot_invent_a_stricter_relation(source_relation):
    _, errors = driver_for(
        DUO
        + f"""
    def strengthen (d:(Duo Int){source_relation}) : (Duo Int){{|fun x => fun y => x < y|}} := d;
    """
    )
    assert errors


def test_relation_can_be_forgotten():
    _, errors = driver_for(
        DUO
        + """
    def forget (d:(Duo Int){|fun x => fun y => x < y|}) : (Duo Int) := d;
    """
    )
    assert not errors


@pytest.mark.parametrize("predicate", ["fun x => true", "fun x => fun y => x + y", "fun x => fun y => x && y"])
def test_malformed_relation_rejected(predicate):
    _, errors = driver_for(DUO + f"def invalid : (Duo Int){{|{predicate}|}} := Duo.mk 1 2;")
    assert errors


def test_two_relation_arguments_remain_distinct():
    source = """
    inductive Triple forall <r:Int -> Int -> Bool> forall <s:Int -> Int -> Bool>
    | mk (x:Int) (y:{v:Int | r x v}) (z:{v:Int | s y v}) : Triple{|r|}{|s|}
    def triple : Triple{|fun x => fun y => x < y|}{|fun x => fun y => x > y|} := Triple.mk 1 3 2;
    """
    assert not driver_for(source)[1]
    assert driver_for(source.replace("Triple.mk 1 3 2", "Triple.mk 1 3 4"))[1]


def test_opaque_relation_survives_matching():
    _, errors = driver_for(
        DUO
        + """
    def second : forall a:B, forall <q:a -> a -> Bool>,
        (d:(Duo a){|q|}) -> {v:a | q (Duo.firstValue d) v} :=
        Λ a:B => Λ <q:a -> a -> Bool> => fun d =>
        match d with | mk first second => second;
    """
    )
    assert not errors


def test_synquid_synthesizes_match_using_relation():
    driver, errors = driver_for(
        DUO
        + """
    def second (d:(Duo Int){|fun x => fun y => x < y|}) : {v:Int | v > Duo.firstValue d} := ?body;
    def main (u:Int):Int := second (Duo.mk 4 7);
    """
    )
    assert not errors
    assert driver.has_synth()
    driver.synth()
    assert driver.run() == 7


def test_predicate_substitution_avoids_capture():
    x, y = Name("x", 101), Name("y", 102)
    predicate = LiquidPredicate((x,), LiquidApp(Name("<", 0), [LiquidVar(x), LiquidVar(y)]))
    ty = TypeConstructor(Name("Box", 103), [t_int], refinements=[predicate])
    changed = substitution_liquid_in_type(ty, LiquidVar(x), y)
    assert changed.refinements[0].parameters != (x,)
    z = LiquidVar(Name("z", 104))
    assert changed.refinements[0].apply([z]) == LiquidApp(Name("<", 0), [z, LiquidVar(x)])


def test_predicate_application_is_simultaneous():
    x, y = Name("x", 101), Name("y", 102)
    predicate = LiquidPredicate((x, y), LiquidApp(Name("<", 0), [LiquidVar(x), LiquidVar(y)]))
    assert predicate.apply([LiquidVar(y), LiquidVar(x)]) == LiquidApp(Name("<", 0), [LiquidVar(y), LiquidVar(x)])


def test_synquid_synthesizes_polymorphic_relation_reversal():
    from pathlib import Path

    source = Path("examples/synthesis/synquid/relational_swap.ae").read_text()
    driver, errors = driver_for(source)
    assert not errors
    assert driver.has_synth()
    driver.synth()
    assert driver.run() == ("Duo_mk", 2, 1)


def test_paper_relational_list_reverse_checks_and_runs():
    from pathlib import Path

    driver, errors = driver_for(Path("examples/synthesis/synquid/relational_reverse.ae").read_text())
    assert not errors
    assert driver.run() == ("RList_cons", 3, ("RList_cons", 2, ("RList_cons", 1, ("RList_nil",))))


@pytest.mark.parametrize("body", ["xs", "reverse{a}{|fun u => fun v => r u v|} xs"])
def test_relation_reversal_rejects_identity_and_nondecreasing_recursion(body):
    from pathlib import Path

    source = Path("examples/synthesis/synquid/relational_reverse.ae").read_text()
    start = source.index("    match xs with", source.index("def reverse"))
    end = source.index(";", start)
    source = source[:start] + body + source[end:]
    assert driver_for(source)[1]


def test_unchecked_recursion_cannot_create_a_relation():
    _, errors = driver_for(
        DUO
        + """
    def invent (d:(Duo Int)) : (Duo Int){|fun x => fun y => x < y|} := invent d;
    """
    )
    assert errors


def test_predicates_can_have_more_than_two_arguments():
    source = """
    inductive Triple forall <r:Int -> Int -> Int -> Bool>
    | mk (x:Int) (y:Int) (z:{v:Int | r x y v}) : Triple{|r|}
    def triple : Triple{|fun x => fun y => fun z => x + y = z|} := Triple.mk{|fun x => fun y => fun z => x + y = z|} 1 2 3;
    """
    assert not driver_for(source)[1]
    assert driver_for(source.replace("1 2 3;", "1 2 4;"))[1]


def test_relation_type_survives_surface_core_and_print_roundtrip():
    from aeon.sugar.parser import parse_type
    from aeon.sugar.lifting import lift_type
    from aeon.sugar.lowering import type_to_core
    from aeon.sugar.equality import type_equality
    from aeon.utils.pprint import pretty_print_stype

    original = parse_type("(Duo Int){|fun x => fun y => x < y|}")
    lifted = lift_type(type_to_core(original))
    assert type_equality(original, lifted)
    assert type_equality(lifted, parse_type(pretty_print_stype(lifted)))


def test_relation_type_alpha_equivalence_and_cache_keys():
    from aeon.core.equality import core_type_equality, canonicalize_type

    x, y, a, b = [Name(n, 100 + i) for i, n in enumerate(["x", "y", "a", "b"])]

    def relation(first, second, operator):
        return TypeConstructor(
            Name("Duo", 105),
            [t_int],
            refinements=[
                LiquidPredicate((first, second), LiquidApp(Name(operator, 0), [LiquidVar(first), LiquidVar(second)]))
            ],
        )

    left, renamed, different = relation(x, y, "<"), relation(a, b, "<"), relation(x, y, ">")
    assert core_type_equality(left, renamed)
    assert canonicalize_type(left) == canonicalize_type(renamed)
    assert not core_type_equality(left, different)
    assert len({canonicalize_type(left), canonicalize_type(renamed), canonicalize_type(different)}) == 2


def test_qualifier_unification_rejects_recursive_sort_equations():
    from aeon.core.types import TypeVar, t_bool
    from aeon.typechecking.liquid import LiquidTypeCheckingContext, LiquidTypeCheckException, type_infer_liquid

    a, x, xs, r = [Name(n, 200 + i) for i, n in enumerate(["a", "x", "xs", "r"])]
    variable = TypeVar(a)
    ctx = LiquidTypeCheckingContext(
        [], {x: variable, xs: TypeConstructor(Name("List", 210), [variable])}, {r: [variable, variable, t_bool]}
    )
    with pytest.raises(LiquidTypeCheckException):
        type_infer_liquid(ctx, LiquidApp(r, [LiquidVar(xs), LiquidVar(x)]))


@pytest.mark.parametrize("body,valid", [("second", True), ("first", False)])
def test_matching_constructed_value_retains_inferred_predicate(body, valid):
    _, errors = driver_for(
        DUO
        + f"""
    def answer : {{v:Int | v > 1}} := match Duo.mk 1 2 with | mk first second => {body};
    """
    )
    assert (not errors) == valid


def test_relation_checks_function_preconditions():
    _, errors = driver_for(
        DUO
        + """
    def positive (x:{v:Int | v > 0}) : Bool := true;
    def invalid : (Duo Int){|fun x => fun y => positive x|} := Duo.mk 1 2;
    """
    )
    assert errors
    assert "precondition" in str(errors[0]).lower()


def test_import_preserves_datatype_predicate_parameters(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "Duo.ae").write_text(DUO)
    main = tmp_path / "main.ae"
    main.write_text("""
    import Duo;
    def second (d:(Duo Int){|fun x => fun y => x < y|}) :
        {v:Int | v > Duo.firstValue d} := match d with | Duo.mk first second => second;
    def main (u:Int):Int := second (Duo.mk 3 9);
    """)
    driver = AeonDriver(AeonConfig("synquid", SilentSynthesisUI(), 20))
    assert not list(driver.parse(filename=str(main)))
    assert driver.run() == 9


def test_named_relation_can_be_passed_to_polymorphic_constructor():
    driver, errors = driver_for(
        DUO
        + """
    def make : forall a:B, forall <r:a -> a -> Bool>,
        (x:a) -> (y:{v:a | r x v}) -> (Duo a){|r|} :=
        Λ a:B => Λ <r:a -> a -> Bool> => fun x => fun y => Duo.mk{a}{|r|} x y;
    def main (u:Int) : (Duo Int){|fun x => fun y => x < y|} :=
        make{Int}{|fun x => fun y => x < y|} 1 2;
    """
    )
    assert not errors
    assert driver.run() == ("Duo_mk", 1, 2)
