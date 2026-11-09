"""Term and refinement productions remain distinct through recursive expansion."""

import pytest

from aeon.core.liquid import LiquidApp, LiquidVar
from aeon.core.substitutions import liquefy
from aeon.core.terms import Abstraction, Application, RefinementApplication, TypeApplication, Var
from aeon.core.types import AbstractionType, RefinedType, RefinementPolymorphism, t_bool, t_int
from aeon.synthesis.grammar.nonterminals import ExpressionDomain, GrammarScope, Nonterminal
from aeon.synthesis.modules.native_search import initial_partial, literal_completions
from aeon.synthesis.modules.tdsyn.actions import (
    backward_app_candidates,
    backward_close_candidates,
    backward_if_candidates,
    forward_let_abs_candidates,
    forward_let_app_candidates,
    forward_let_if_candidates,
    forward_let_tabs_candidates,
    forward_let_tapp_candidates,
)
from aeon.synthesis.modules.tdsyn.library import get_component_library
from aeon.synthesis.modules.tdsyn.worklist import expand_at_hole
from aeon.typechecking.context import ReflectedBinder, TypingContext
from aeon.typechecking.liquid import lower_context, type_infer_liquid
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name

TERM, REFINEMENT = ExpressionDomain.TERM, ExpressionDomain.REFINEMENT
P, X, ARG = Name("p", 101), Name("x", 102), Name("arg", 103)
SORT = AbstractionType(ARG, t_int, t_bool)


def head(term):
    while isinstance(term, (Application, TypeApplication, RefinementApplication)):
        term = term.fun if isinstance(term, Application) else term.body
    assert isinstance(term, Var)
    return term.name


def test_component_productions_and_caches_are_separate_for_the_same_type():
    projection, runtime, reflected = Name("project", 104), Name("apply", 105), Name("reflected", 106)
    ctx = (
        TypingContext()
        .with_refinement(P, SORT)
        .with_var(X, t_int)
        .with_uninterpreted(projection, AbstractionType(ARG, t_int, t_int))
        .with_var(runtime, AbstractionType(ARG, SORT, t_bool))
    )
    ctx.entries.append(ReflectedBinder(reflected, SORT, (ARG,), LiquidApp(P, [LiquidVar(ARG)])))
    scope = GrammarScope.from_context(ctx)
    assert set(dict(scope.terms)) == {X, runtime, reflected}
    assert set(dict(scope.refinements)) == {X, P, projection, reflected}
    assert Nonterminal(TERM, t_bool) != Nonterminal(REFINEMENT, t_bool)
    for domain in [TERM, REFINEMENT, REFINEMENT, TERM]:
        library = get_component_library(ctx, lambda _: False, domain=domain)
        names = {head(t) for t, _ in library.functions_returning(t_bool)}
        assert names == ({runtime, reflected} if domain is TERM else {P, reflected})


def test_shadowing_is_resolved_before_either_domain_gets_productions():
    outer, inner = Name("p", 100), Name("p", 104)
    ctx = TypingContext().with_var(outer, SORT).with_refinement(P, SORT)
    scope = GrammarScope.from_context(ctx)
    assert scope.terms == ()
    assert scope.refinements == ((P, SORT),)
    scope = GrammarScope.from_context(ctx.with_var(inner, t_bool))
    assert scope.terms == scope.refinements == ((inner, t_bool),)


def test_refinement_application_production_cannot_leak_into_a_term_argument():
    accepts = Name("accepts", 104)
    ctx = TypingContext().with_refinement(P, SORT).with_var(X, t_int)
    ctx = ctx.with_var(accepts, AbstractionType(ARG, t_bool, t_int))
    initial = initial_partial(ctx, t_int, TERM)
    term, children = next(
        c for c in backward_app_candidates(initial.holes[0], lambda _: False) if head(c[0]) == accepts
    )
    partial = expand_at_hole(initial, initial.holes[0], term, children, 1)
    assert partial.holes[0].nonterminal == Nonterminal(TERM, t_bool)
    assert all(head(term) != P for term, _ in backward_app_candidates(partial.holes[0], lambda _: False))

    logical = initial_partial(ctx, t_bool, REFINEMENT)
    term, children = next(c for c in backward_app_candidates(logical.holes[0], lambda _: False) if head(c[0]) == P)
    partial = expand_at_hole(logical, logical.holes[0], term, children, 1)
    assert partial.holes[0].nonterminal == Nonterminal(REFINEMENT, t_int)
    assert literal_completions(partial) == []
    [(value, remaining)] = backward_close_candidates(partial.holes[0], lambda _: False)
    complete = expand_at_hole(partial, partial.holes[0], value, remaining, 1)
    assert complete.is_complete()
    predicate = liquefy(complete.term)
    assert predicate == LiquidApp(P, [LiquidVar(X)])
    assert type_infer_liquid(lower_context(ctx), predicate) == t_bool
    assert not check_type(ctx, complete.term, t_bool)


@pytest.mark.parametrize("domain", [TERM, REFINEMENT])
def test_lambda_and_conditional_children_keep_their_domain(domain):
    initial = initial_partial(TypingContext().with_refinement(P, SORT), SORT, domain)
    assert isinstance(initial.term, Abstraction)
    hole = initial.holes[0]
    assert hole.nonterminal == Nonterminal(domain, t_bool)
    [(term, children)] = backward_if_candidates(hole, lambda _: False)
    nested = expand_at_hole(initial, hole, term, children, 1)
    assert all(child.nonterminal == Nonterminal(domain, t_bool) for child in nested.holes)


def test_generated_logical_predicate_is_accepted_only_at_an_erased_boundary():
    q, result, function = Name("q", 104), Name("result", 105), Name("keep", 106)
    actual = RefinedType(result, t_int, LiquidApp(P, [LiquidVar(result)]))
    formal = RefinedType(result, t_int, LiquidApp(q, [LiquidVar(result)]))
    ctx = TypingContext().with_refinement(P, SORT).with_var(X, actual)
    ctx = ctx.with_var(function, RefinementPolymorphism(q, SORT, AbstractionType(ARG, formal, formal)))
    initial = initial_partial(ctx, SORT, REFINEMENT)
    hole = initial.holes[0]
    term, children = next(c for c in backward_app_candidates(hole, lambda _: False) if head(c[0]) == P)
    partial = expand_at_hole(initial, hole, term, children, 1)
    term, children = next(c for c in backward_close_candidates(partial.holes[0], lambda _: False) if c[0] == Var(ARG))
    predicate = expand_at_hole(partial, partial.holes[0], term, children, 1).term
    assert check_type(ctx, Application(RefinementApplication(Var(function), predicate), Var(X)), actual)


@pytest.mark.parametrize(
    "action",
    [
        forward_let_abs_candidates,
        forward_let_app_candidates,
        forward_let_if_candidates,
        forward_let_tabs_candidates,
        forward_let_tapp_candidates,
    ],
)
def test_runtime_binding_productions_are_not_in_the_refinement_grammar(action):
    partial = initial_partial(TypingContext().with_refinement(P, SORT), t_bool, REFINEMENT)
    assert action(partial.holes[0], lambda _: False) == []
