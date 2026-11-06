"""Polymorphic values must not bypass concrete or quantified refinements."""

import pytest

from aeon.core.parser import parse_type
from aeon.core.terms import Abstraction, Annotation, Hole, Literal, RefinementApplication, TypeApplication, Var
from aeon.core.types import Kind, RefinementPolymorphism, TypePolymorphism, t_bool, t_int
from aeon.elaboration.context import build_typing_context
from aeon.prelude.prelude import typing_vars
from aeon.sugar.lowering import lower_to_core_context
from aeon.synthesis.tactics.subtyping import fits
from aeon.typechecking.entailment import entailment
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from aeon.verification.sub import sub


def context():
    return lower_to_core_context(build_typing_context(typing_vars))


def predicate_poly(name, body, sort="(x:Int) -> Bool"):
    return RefinementPolymorphism(Name(name), parse_type(sort), parse_type(body))


@pytest.mark.parametrize("refinement", [False, True])
def test_polymorphic_zero_cannot_prove_a_positive_result(refinement):
    ty = predicate_poly("p", "{v:Int | v == 0}") if refinement else parse_type("forall a:B, {v:Int | v == 0}")
    name = Name("zero")
    ctx = context().with_var(name, ty)
    goal = parse_type("{v:Int | v > 0}")
    assert not fits(ctx, ty, goal)
    assert not check_type(ctx, Var(name), goal)


@pytest.mark.parametrize("refinement", [False, True])
def test_explicit_instantiation_retains_the_result_refinement(refinement):
    ty = predicate_poly("p", "{v:Int | v == 0}") if refinement else parse_type("forall a:B, {v:Int | v == 0}")
    name = Name("zero")
    ctx = context().with_var(name, ty)
    value = (
        RefinementApplication(Var(name), Abstraction(Name("x"), Literal(True, t_bool)))
        if refinement
        else TypeApplication(Var(name), t_int)
    )
    assert check_type(ctx, value, parse_type("{v:Int | v == 0}"))
    assert not check_type(ctx, value, parse_type("{v:Int | v > 0}"))


@pytest.mark.parametrize(
    "actual,goal,valid",
    [
        ("forall a:B, (x:a) -> a", "forall b:B, (y:b) -> b", True),
        ("forall a:B, (x:a) -> Int", "forall b:B, (y:b) -> Bool", False),
        ("forall a:B, {v:Int | v == 0}", "forall b:B, {v:Int | v >= 0}", True),
        ("forall a:B, {v:Int | v == 0}", "forall b:B, {v:Int | v > 0}", False),
        ("forall a:B, a", "forall b:*, b", False),
    ],
)
def test_quantified_type_bodies_are_checked(actual, goal, valid):
    ctx = context()
    assert entailment(ctx, sub(ctx, parse_type(actual), parse_type(goal))) is valid


@pytest.mark.parametrize("stronger", [False, True])
def test_quantified_predicate_bodies_are_checked(stronger):
    actual = predicate_poly("p", "(x:{v:Int | p v}) -> {v:Int | p v}")
    goal = predicate_poly(
        "q", "(x:{v:Int | q v}) -> {v:Int | q v && v > 0}" if stronger else "(x:{v:Int | q v}) -> {v:Int | q v}"
    )
    ctx = context()
    assert entailment(ctx, sub(ctx, actual, goal)) is (not stronger)


def test_quantified_predicate_sort_mismatch_is_rejected():
    actual = predicate_poly("p", "Int")
    goal = predicate_poly("q", "Int", "(x:Bool) -> Bool")
    assert not entailment(context(), sub(context(), actual, goal))


@pytest.mark.parametrize("refinement", [False, True])
@pytest.mark.parametrize("wrapper", ["variable", "annotation", "type_application"])
def test_quantified_aliases_preserve_valid_refinements(refinement, wrapper):
    actual = predicate_poly("p", "{v:Int | v == 0}") if refinement else parse_type("forall a:B, {v:Int | v == 0}")
    goal = predicate_poly("q", "{v:Int | v >= 0}") if refinement else parse_type("forall b:B, {v:Int | v >= 0}")
    name = Name("zero")
    ctx = context().with_var(name, actual)
    term = Var(name)
    if wrapper == "annotation":
        term = Annotation(term, actual)
    elif wrapper == "type_application":
        ctx = context().with_var(name, TypePolymorphism(Name("unused"), Kind.BASE, actual))
        term = TypeApplication(Var(name), t_int)
    assert check_type(ctx, term, goal)


def test_legacy_predicate_domain_matches_full_sort():
    actual = RefinementPolymorphism(Name("p"), t_int, t_int)
    assert entailment(context(), sub(context(), actual, predicate_poly("q", "Int")))


def test_open_holes_still_check_against_refinements():
    assert check_type(context(), Hole(Name("body")), parse_type("{v:Int | v > 0}"))
