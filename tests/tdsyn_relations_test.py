"""Retained constructor relations participate in type-directed generation."""

import pytest

from aeon.core.predicates import predicate_from_term
from aeon.core.terms import Application, RefinementApplication, TypeApplication, Var
from aeon.core.types import RefinedType, top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.modules.tdsyn.helpers import base_type_of, get_return_type, monomorphize
from aeon.synthesis.modules.tdsyn.library import get_component_library
from aeon.synthesis.uis.api import SilentSynthesisUI


DUO = """
    inductive Duo a forall <r:a -> a -> Bool>
    | mk (first:a) (second:{v:a | r first v}):
        {d:(Duo a){|r|} | Duo.firstValue d = first}
    + firstValue (d:(Duo a)):a
"""


def _driver(source, backend="tdsyn", budget=10):
    driver = AeonDriver(AeonConfig(backend, SilentSynthesisUI(), budget))
    assert not driver.parse(aeon_code=source)
    assert driver.has_synth()
    return driver


def _hole_info(driver):
    targets = {hole for _, holes in driver.incomplete_functions for hole in holes}
    info = get_holes_info(driver.typing_ctx, driver.core, top, driver.incomplete_functions, refined_types=True)
    return {name: entry for name, entry in info.items() if name in targets}


@pytest.mark.parametrize("backend", ["tdsyn_enumerative", "tdsyn_backward", "tdsyn_random"])
def test_binary_constructor_relation_is_synthesized(backend):
    driver = _driver(
        DUO
        + """
        def main (u:Int):{d:(Duo Int){|fun x => fun y => x < y|} | Duo.firstValue d = 4} := ?pair;
    """,
        backend,
    )
    driver.synth()
    tag, first, second = driver.run()
    assert tag == "Duo_mk"
    assert first == 4
    assert second > first


@pytest.mark.parametrize("arity", [1, 2, 3])
def test_unconstrained_search_predicate_keeps_its_declared_arity(arity):
    from aeon.core.liquid import LiquidLiteralBool, LiquidLiteralInt

    fields = " ".join(f"(x{i}:Int)" for i in range(arity - 1))
    fields += f" (x{arity - 1}:{{v:Int | r {' '.join(f'x{i}' for i in range(arity - 1))} v}})"
    driver = _driver(f"""
        inductive Values forall <r:{"Int -> " * arity}Bool>
        | mk {fields}:Values{{|r|}}
        def main (u:Int):Values := ?values;
    """)
    with driver.session.activate():
        _, ctx = next(iter(_hole_info(driver).values()))
        name, ty = next((n, t) for n, t in ctx.vars() if n.name == "Values_mk")
        [(_, instantiated)] = monomorphize(name, ty, ctx)
        result = base_type_of(get_return_type(instantiated))
        assert result is not None
        assert result.refinements[0].apply([LiquidLiteralInt(0)] * arity) == LiquidLiteralBool(True)


MASK = """
    inductive Mask forall <fits:Int -> Int -> Bool>
    | empty:{m:Mask{|fits|} | Mask.count m = 0 && Mask.weight m = 0}
    | cons (rest:Mask{|fits|}) (used:{b:Bool | fits (if b then 1 else 0) (Mask.weight rest)}):
        {m:Mask{|fits|} | Mask.count m = Mask.count rest + 1 &&
            Mask.weight m = Mask.weight rest + (if used then 1 else 0)}
    + count (m:Mask):Int
    + weight (m:Mask):Int
"""


@pytest.mark.parametrize("size", [0, 3])
def test_recursive_relation_keeps_count_and_weight_constraints(size):
    driver = _driver(
        MASK
        + f"""
        def main (u:Int):{{m:Mask{{|fun w => fun rest => w + rest <= 1|}} |
            Mask.count m = {size} && Mask.weight m = {min(size, 1)}}} := ?mask;
    """
    )
    driver.synth()
    value = driver.run()
    decisions = []
    while value[0] == "Mask_cons":
        _, value, used = value
        decisions.append(used)
    assert value == ("Mask_empty",)
    assert len(decisions) == size
    assert sum(decisions) == min(size, 1)


def test_goal_specialization_does_not_reuse_another_relation_from_cache():
    driver = _driver(
        DUO
        + """
        def less:(Duo Int){|fun x => fun y => x < y|} := ?less;
        def greater:(Duo Int){|fun x => fun y => x > y|} := ?greater;
    """
    )
    from aeon.core.equality import core_type_equality

    with driver.session.activate():
        info = _hole_info(driver)
        goals = [ty for ty, _ in info.values()]
        ctx = list(info.values())[-1][1]
        for goal in [*goals, *reversed(goals)]:
            library = get_component_library(ctx, lambda _: False, goal)
            matches = [
                (term, ty)
                for term, ty in library.functions_returning(goal)
                if _head(term) == "Duo_mk" and core_type_equality(base_type_of(get_return_type(ty)), base_type_of(goal))
            ]
            assert len(matches) == 1


def _head(term):
    while isinstance(term, (Application, TypeApplication, RefinementApplication)):
        term = term.fun if isinstance(term, Application) else term.body
    assert isinstance(term, Var)
    return term.name.name


def test_reordered_relations_are_matched_by_identity():
    driver = _driver("""
        inductive Triple forall <r:Int -> Int -> Bool> forall <s:Int -> Int -> Bool>
        | mk (x:Int) (y:{v:Int | r x v}) (z:{v:Int | s y v}):Triple{|r|}{|s|}
        def reversed:forall <p:Int -> Int -> Bool>, forall <q:Int -> Int -> Bool>,
            (t:Triple{|q|}{|p|}) -> Triple{|q|}{|p|} :=
            Λ <p:Int -> Int -> Bool> => Λ <q:Int -> Int -> Bool> => fun t => t;
        def main (u:Int):Triple{|fun x => fun y => x < y|}{|fun x => fun y => x > y|} := ?triple;
    """)
    from aeon.core.equality import core_liquid_equality

    with driver.session.activate():
        goal, ctx = next(iter(_hole_info(driver).values()))
        name, ty = next((n, t) for n, t in ctx.vars() if n.name == "reversed")
        [(term, _)] = monomorphize(name, ty, ctx, goal)
        assert isinstance(term, RefinementApplication)
        q = predicate_from_term(term.refinement)
        assert isinstance(term.body, RefinementApplication)
        p = predicate_from_term(term.body.refinement)
        base = goal.type if isinstance(goal, RefinedType) else goal
        for actual, expected in zip((q, p), base.refinements):
            assert core_liquid_equality(actual.body, expected.body, dict(zip(actual.parameters, expected.parameters)))


@pytest.mark.parametrize("second,valid", [(3, False), (4, False), (5, True)])
def test_instantiated_constructor_still_checks_its_relation(second, valid):
    from aeon.core.terms import Literal
    from aeon.core.types import t_int
    from aeon.typechecking.typeinfer import check_type

    driver = _driver(
        DUO
        + """
        def main (u:Int):{d:(Duo Int){|fun x => fun y => x < y|} | Duo.firstValue d = 4} := ?pair;
    """
    )
    with driver.session.activate():
        goal, ctx = next(iter(_hole_info(driver).values()))
        library = get_component_library(ctx, lambda _: False, goal)
        constructor = next(
            term
            for term, ty in library.functions_returning(goal)
            if _head(term) == "Duo_mk" and base_type_of(get_return_type(ty)).args == [t_int]
        )
        candidate = Application(Application(constructor, Literal(4, t_int)), Literal(second, t_int))
        assert check_type(ctx, candidate, goal) is valid


def test_ternary_goal_relation_is_synthesized():
    driver = _driver("""
        inductive Triple forall <r:Int -> Int -> Int -> Bool>
        | mk (x:{v:Int | v = 2}) (y:{v:Int | v = 3}) (z:{v:Int | r x y v}):Triple{|r|}
        def main (u:Int):Triple{|fun x => fun y => fun z => z = x + y|} := ?triple;
    """)
    driver.synth()
    assert driver.run() == ("Triple_mk", 2, 3, 5)


def test_goal_relation_can_reference_a_function_parameter():
    driver = _driver(
        DUO
        + """
        def pair (limit:Int):(Duo Int){|fun x => fun y => y = limit|} := ?pair;
        def main (u:Int):(Duo Int){|fun x => fun y => y = 7|} := pair 7;
    """,
        # Solving a relation under a lexical parameter exercises several
        # refinement checks; allow CPU contention in the full CI suite.
        budget=60,
    )
    driver.synth()
    assert driver.run()[2] == 7


def test_opaque_predicate_is_kept_in_a_nullary_constructor():
    driver = _driver(
        MASK
        + """
        def empty:forall <q:Int -> Int -> Bool>, {m:Mask{|q|} | Mask.count m = 0} :=
            Λ <q:Int -> Int -> Bool> => ?empty;
        def main (u:Int):Mask{|fun w => fun rest => w + rest <= 1|} :=
            empty{|fun w => fun rest => w + rest <= 1|};
    """
    )
    driver.synth()
    assert driver.run() == ("Mask_empty",)
