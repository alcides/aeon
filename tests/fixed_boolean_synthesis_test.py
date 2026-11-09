"""Fixed-size relational data remains a searchable Boolean product."""

from itertools import islice

import pytest

from aeon.backend.evaluator import eval
from aeon.core.substitutions import substitution
from aeon.core.terms import ImplicitRefinementHole, RefinementApplication
from aeon.core.types import t_int
from aeon.synthesis.fixed_data import FixedBooleanList
from aeon.synthesis.modules.tdsyn.library import visible_vars
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from tests.tdsyn_relations_test import MASK, _driver, _hole_info


def decisions(value):
    result = []
    while value[0] == "Mask_cons":
        _, value, used = value
        assert type(used) is bool
        result.append(used)
    assert value == ("Mask_empty",)
    return result


def source(size, capacity):
    return (
        MASK
        + f"""
        def main (u:Int):{{m:Mask{{|fun w => fun rest => w + rest <= {capacity}|}} |
            Mask.count m = {size} && Mask.weight m <= {capacity}}} := ?solution;
    """
    )


def run_candidate(driver, term):
    target = driver.incomplete_functions[0][1][0]
    return eval(substitution(driver.core, term, target), driver.evaluation_ctx)


@pytest.mark.parametrize("backend", ["gp", "synquid"])
@pytest.mark.parametrize("size", [0, 3])
def test_backend_returns_a_valid_relational_mask(backend, size):
    driver = _driver(source(size, 1), backend)
    driver.synth()
    bits = decisions(driver.run())
    assert len(bits) == size and sum(bits) <= 1


def test_all_fifty_genes_control_the_corresponding_boolean():
    driver = _driver(source(50, 50))
    with driver.session.activate():
        goal, ctx = next(iter(_hole_info(driver).values()))
        space = FixedBooleanList.build(ctx, goal, lambda _: False)
        assert space is not None and len(space.expansion.leaves) == 50
        # Construction is tail-first; every gene remains independently visible.
        for genome in [[0] * 50, [1] * 50, [i % 2 for i in range(50)]]:
            term = space.decode(genome)
            assert term is not None
            assert decisions(run_candidate(driver, term)) == list(reversed([bool(g) for g in genome]))
            assert check_type(ctx, term, goal)


def test_decoder_repairs_capacity_and_enumerator_returns_distinct_valid_masks():
    # Only the retained field relation enforces capacity one here.
    driver = _driver(source(4, 1).replace("Mask.weight m <= 1", "Mask.weight m <= 4"))
    with driver.session.activate():
        goal, ctx = next(iter(_hole_info(driver).values()))
        space = FixedBooleanList.build(ctx, goal, lambda _: False)
        assert space is not None
        term = space.decode([1] * 4)
        assert term is not None
        assert sum(decisions(run_candidate(driver, term))) == 1
        assert check_type(ctx, term, goal)
        candidates = list(islice(space.candidates(), 10))
        assert len(candidates) == 5
        assert len({tuple(decisions(run_candidate(driver, t))) for t in candidates}) == 5
        assert all(check_type(ctx, t, goal) for t in candidates)


def test_impossible_or_expired_list_does_not_produce_a_candidate():
    driver = _driver(source(3, "(0 - 1)"))
    with driver.session.activate():
        goal, ctx = next(iter(_hole_info(driver).values()))
        space = FixedBooleanList.build(ctx, goal, lambda _: False)
        assert space is not None
        assert space.decode([1, 0, 1]) is None
        assert list(space.candidates()) == []
        space.deadline = 0
        assert space.decode([0]) is None


def test_non_runtime_bindings_shadow_but_never_enter_native_grammar():
    name = Name("projection", 42)
    ctx = TypingContext().with_var(name, t_int).with_uninterpreted(Name("projection", 43), t_int)
    assert not visible_vars(ctx)


def test_synquid_materializes_the_solved_predicate_in_constructor_terms():
    from aeon.synthesis.modules.synquid.constraints import ConstraintState
    from aeon.synthesis.modules.synquid.engine import _eliminations
    from aeon.synthesis.modules.synquid.round_trip import erase

    driver = _driver(source(0, 1))
    with driver.session.activate():
        goal, ctx = next(iter(_hole_info(driver).values()))
        terms = list(_eliminations(ctx, 0, erase(goal), lambda _: False, {}, ConstraintState(ctx)))
        assert terms
        for term in terms:
            assert isinstance(term, RefinementApplication)
            assert not isinstance(term.refinement, ImplicitRefinementHole)
            assert check_type(ctx, term, erase(goal))


def test_tail_preconditions_are_not_lost_when_unrolling_the_spine():
    driver = _driver(source(3, 3).replace("(rest:Mask{|fits|})", "(rest:{m:Mask{|fits|} | Mask.count m < 2})"))
    with driver.session.activate():
        goal, ctx = next(iter(_hole_info(driver).values()))
        space = FixedBooleanList.build(ctx, goal, lambda _: False)
        assert space is not None
        assert space.decode([0]) is None
        assert list(space.candidates()) == []


def test_match_predicates_are_elaborated_and_unsolved_horns_are_not_emitted():
    from aeon.core.liquid import LiquidPredicate, LiquidVar
    from aeon.core.types import LiquidHornApplication, RefinementPolymorphism
    from aeon.synthesis.modules.synquid.patterns import _predicate_term
    from aeon.synthesis.modules.tdsyn.helpers import base_type_of

    driver = _driver(source(0, 1))
    with driver.session.activate():
        goal, ctx = next(iter(_hole_info(driver).values()))
        schema = next(t for n, t in ctx.vars() if n.name == "Mask_cons")
        assert isinstance(schema, RefinementPolymorphism)
        predicate = base_type_of(goal).refinements[0]
        term = _predicate_term(predicate, {}, ctx, schema.sort)
        assert term is not None and check_type(ctx, term, schema.sort)
        p, x, y = Name("external", 99001), Name("x", 99002), Name("y", 99003)
        unresolved = LiquidPredicate((x, y), LiquidHornApplication(p, [(LiquidVar(x), t_int), (LiquidVar(y), t_int)]))
        assert _predicate_term(unresolved, {}, ctx, schema.sort) is None
