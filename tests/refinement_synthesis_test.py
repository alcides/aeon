"""Scoped abstract predicates must survive hole identification without becoming code."""

import pytest

from aeon.core.bind import bind_ctx
from aeon.core.liquid import LiquidApp, LiquidVar
from aeon.core.substitutions import substitution_liquid_in_term
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Literal,
    RefinementAbstraction,
    RefinementApplication,
    TypeApplication,
    Var,
)
from aeon.core.types import AbstractionType, RefinedType, RefinementPolymorphism, t_bool, t_int, top
from aeon.synthesis.entrypoint import make_program, make_validator
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.synquid.guards import bool_terms_from_qualifier_atoms
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.modules.tdsyn.library import get_component_library, visible_vars
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import RefinementBinder, TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from tests.driver import check_and_return_core


KEEP = """
def keep : forall <p : Int -> Bool>, (x : Int<p>) -> Int<p> :=
    Λ <p : Int -> Bool> => fun x => ?body;
def main (args:Int) : Int := keep 5;
"""


def _refined(predicate, *prefix):
    value = Name("v", 10)
    return RefinedType(value, t_int, LiquidApp(predicate, [*(LiquidVar(n) for n in prefix), LiquidVar(value)]))


def _predicate_sort(arity=1):
    result = t_bool
    for index in reversed(range(arity)):
        result = AbstractionType(Name("arg", 100 + index), t_int, result)
    return result


def _compiled_hole():
    program, ctx, _, _ = check_and_return_core(KEEP)
    hole, (goal, local) = next(
        (name, info) for name, info in get_holes_info(ctx, program, top, [], True).items() if name.name == "body"
    )
    owner = next(name for name, holes in incomplete_functions_and_holes(ctx, program) if hole in holes)
    return program, ctx, hole, goal, local, owner


def test_preserving_arbitrary_predicate_is_valid_but_incrementing_is_not():
    program, ctx, hole, goal, local, _ = _compiled_hole()
    x = next(name for name, _ in local.concrete_vars() if name.name == "x")
    plus = next(name for name, _ in local.concrete_vars() if name.name == "+")
    increment = Application(Application(TypeApplication(Var(plus), t_int), Var(x)), Literal(1, t_int))
    validate = make_validator(ctx, make_program(program, hole))
    assert check_type(local, Var(x), goal)
    assert validate(Var(x))
    assert not check_type(local, increment, goal)
    assert not validate(increment)


def test_candidates_cannot_call_erased_predicates_at_runtime():
    program, ctx, hole, _, local, _ = _compiled_hole()
    p = next(entry.name for entry in local.entries if isinstance(entry, RefinementBinder))
    x = next(name for name, _ in local.concrete_vars() if name.name == "x")
    call = Application(Var(p), Var(x))
    assert not check_type(local, call, t_bool)
    assert not make_validator(ctx, make_program(program, hole))(If(call, Var(x), Var(x)))


def test_explicit_predicate_arguments_can_forward_logical_parameters():
    p, q, x, y, identity, v = [Name(name, index) for index, name in enumerate(("p", "q", "x", "y", "id", "v"), 1)]
    sort = _predicate_sort()
    identity_type = RefinementPolymorphism(q, sort, AbstractionType(y, _refined(q), _refined(q)))
    ctx = TypingContext().with_var(identity, identity_type).with_refinement(p, sort).with_var(x, _refined(p))
    predicate = Abstraction(v, Application(Var(p), Var(v)))
    call = Application(RefinementApplication(Var(identity), predicate), Var(x))
    # Forwarding p as an erased predicate argument must remain valid even
    # though evaluating p as an executable Boolean function is forbidden.
    assert check_type(ctx, call, _refined(p))


@pytest.mark.parametrize("backend", [TDSynSynthesizer, SynquidSynthesizer])
def test_synthesizes_identity_under_abstract_predicate(backend):
    program, ctx, hole, goal, local, owner = _compiled_hole()
    validate = make_validator(ctx, make_program(program, hole))
    result = backend().synthesize(
        ctx=local,
        type=goal,
        validate=validate,
        evaluate=lambda _: [],
        fun_name=owner,
        metadata={},
        budget=3,
        ui=SilentSynthesisUI(),
    )
    # Equivalent identities such as x / 1 are also valid synthesis results.
    assert result is not None
    assert check_type(local, result, goal)
    assert validate(result)


def test_synquid_synthesizes_refinement_polymorphic_function():
    p, x = Name("p", 1), Name("x", 2)
    sort = _predicate_sort()
    goal = RefinementPolymorphism(p, sort, AbstractionType(x, _refined(p), _refined(p)))
    ctx = TypingContext()
    result = SynquidSynthesizer().synthesize(
        ctx=ctx,
        type=goal,
        validate=lambda term: check_type(ctx, term, goal),
        evaluate=lambda _: [],
        fun_name=Name("keep", 3),
        metadata={},
        budget=3,
        ui=SilentSynthesisUI(),
    )
    assert result == RefinementAbstraction(p, sort, Abstraction(x, Var(x)))
    assert check_type(ctx, result, goal)


@pytest.mark.parametrize("arity", [1, 2, 3])
@pytest.mark.parametrize("annotated", [False, True])
def test_hole_scope_alpha_renames_predicates_and_embedded_annotations(arity, annotated):
    signature, actual, x, hole = Name("spec", 1), Name("actual", 2), Name("x", 3), Name("body", 4)
    prefix = [Name("anchor", 20 + index) for index in range(arity - 1)]
    refined = _refined(signature, *prefix)
    body = Annotation(Hole(hole), refined) if annotated else Hole(hole)
    term = Abstraction(x, body)
    ty = AbstractionType(x, refined, refined)
    for anchor in reversed(prefix):
        term = Abstraction(anchor, term)
        ty = AbstractionType(anchor, t_int, ty)
    sort = _predicate_sort(arity)
    term = RefinementAbstraction(actual, sort, term)
    ty = RefinementPolymorphism(signature, sort, ty)

    goal, ctx = get_holes_info(TypingContext(), term, ty, [], True)[hole]
    assert goal == _refined(actual, *prefix)
    assert RefinementBinder(actual, sort) in ctx.entries
    assert check_type(ctx, Var(x), goal)
    assert not check_type(ctx, Literal(0, t_int), goal)


def test_nested_shadowed_predicates_remain_distinct():
    outer, inner, actual_outer, actual_inner = [Name("p", index) for index in range(1, 5)]
    x, y, hole = Name("x", 5), Name("y", 6), Name("body", 7)
    sort = _predicate_sort()
    inner_ty = RefinementPolymorphism(inner, sort, AbstractionType(y, _refined(inner), _refined(inner)))
    ty = RefinementPolymorphism(outer, sort, AbstractionType(x, _refined(outer), inner_ty))
    term = RefinementAbstraction(
        actual_outer, sort, Abstraction(x, RefinementAbstraction(actual_inner, sort, Abstraction(y, Hole(hole))))
    )
    goal, ctx = get_holes_info(TypingContext(), term, ty, [], True)[hole]
    assert check_type(ctx, Var(y), goal)
    assert not check_type(ctx, Var(x), goal)


def test_predicate_substitution_stops_at_shadowing_refinement_binder():
    p, replacement = Name("p", 1), Name("q", 2)
    term = RefinementAbstraction(p, _predicate_sort(), Annotation(Hole(Name("body", 3)), _refined(p)))
    assert substitution_liquid_in_term(term, LiquidVar(replacement), p) == term


def test_logical_predicates_are_not_executable_components_or_guards():
    outer, p, x = Name("p", 1), Name("p", 2), Name("x", 3)
    ctx = TypingContext().with_var(outer, _predicate_sort()).with_refinement(p, _predicate_sort()).with_var(x, t_int)
    assert p not in dict(ctx.vars())
    assert "p" not in {name.name for name, _ in ctx.concrete_vars()}
    assert "p" not in {name.name for name, _ in visible_vars(ctx)}
    assert not get_component_library(ctx, lambda _: False).functions_returning(t_bool)
    atoms = frozenset({LiquidApp(p, [LiquidVar(x)])})
    assert bool_terms_from_qualifier_atoms(ctx, atoms) == []

    # An ordinary inner value named p remains executable.
    runtime = Name("p", 4)
    inner = ctx.with_var(runtime, t_bool)
    assert (runtime, t_bool) in inner.concrete_vars()
    assert (runtime, t_bool) in visible_vars(inner)


def test_binding_context_preserves_logical_predicates():
    p, x = Name("p", 0), Name("x", 0)
    ctx = TypingContext().with_refinement(p, _predicate_sort()).with_var(x, _refined(p))
    bound, _ = bind_ctx(ctx, [])
    predicate = next(entry for entry in bound.entries if isinstance(entry, RefinementBinder))
    x, ty = next((name, ty) for name, ty in bound.concrete_vars() if name.name == "x")
    assert predicate.name not in dict(bound.vars())
    assert check_type(bound, Var(x), ty)
