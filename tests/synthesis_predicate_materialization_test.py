"""Solved relational predicates survive synthesis materialization."""

from aeon.core.terms import ImplicitRefinementHole, RefinementApplication
from aeon.core.types import t_int
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from tests.tdsyn_relations_test import MASK, _driver, _hole_info


def source(size, capacity):
    return (
        MASK
        + f"""
        def main (u:Int):{{m:Mask{{|fun w => fun rest => w + rest <= {capacity}|}} |
            Mask.count m = {size} && Mask.weight m <= {capacity}}} := ?solution;
    """
    )


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
