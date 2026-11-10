"""Bounded Synquid searches must emit terms accepted by the core checker.

Generate inhabited problems, not arbitrary syntax or filtered successful
results. Every sampled candidate is checked; an empty search also fails.
"""

from itertools import islice

import pytest
from hypothesis import given, note, settings, strategies as st

from aeon.compilation.session import CompilationSession
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Abstraction, Annotation, Application, If, TypeAbstraction, TypeApplication
from aeon.core.types import AbstractionType, Kind, RefinedType, TypePolymorphism, TypeVar, t_bool, t_int
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name


integers = st.integers(-20, 20)
binder_ids = st.integers(1, 10000)


def liquid(operator, *arguments):
    return LiquidApp(Name(operator, 0), list(arguments))


def exact(base, expression):
    result = Name("result", 0)
    return RefinedType(result, base, liquid("==", LiquidVar(result), expression))


def sample_and_check(context, goal, allowed, *, depth=0, conditionals=False, limit=12):
    note(f"Goal: {goal}; components: {[(n, t) for n, t in context.vars() if n.name in allowed]}")
    # Bound the grammar and sample size, rather than relying on a machine's
    # speed. Recursive definitions and datatype matches have separate tests.
    memory = {"synquid_fix": False, "synquid_match_depth": 0}
    with CompilationSession().activate():
        candidates = list(
            islice(
                synthes_memory(
                    context, depth, goal, lambda n: n.name not in allowed, memory, conditionals=conditionals
                ),
                limit,
            )
        )
    assert candidates, "An inhabited generated problem produced no candidates"
    # Do not reuse construction's solver state or filter candidates through the
    # oracle. A single ill-typed emission must falsify and shrink the property.
    with CompilationSession().activate():
        for candidate in candidates:
            note(f"Candidate: {candidate}")
            assert check_type(context, candidate, goal), f"{candidate} does not inhabit {goal}"
    return candidates


@pytest.mark.parametrize("base", [t_int, t_bool], ids=["integer", "boolean"])
@settings(deadline=None)
@given(value=integers, width=st.integers(0, 5), binder_id=binder_ids)
def test_synquid_refined_scalar_candidates_typecheck(base, value, width, binder_id):
    good, bad = Name("good", binder_id), Name("bad", binder_id + 1)
    if base == t_int:
        v = LiquidVar(Name("result", 0))
        goal = RefinedType(
            v.name,
            t_int,
            liquid("&&", liquid(">=", v, LiquidLiteralInt(value)), liquid("<=", v, LiquidLiteralInt(value + width))),
        )
        good_type = exact(base, LiquidLiteralInt(value))
        bad_type = exact(base, LiquidLiteralInt(value + width + 1))
    else:
        goal = good_type = exact(base, LiquidLiteralBool(bool(value % 2)))
        bad_type = exact(base, LiquidLiteralBool(not bool(value % 2)))
    context = built_std_context().with_var(good, good_type).with_var(bad, bad_type)
    sample_and_check(context, goal, {"good", "bad"})


@pytest.mark.parametrize("arity", [1, 2])
@settings(deadline=None)
@given(offset=st.integers(1, 10), lower=integers, binder_id=binder_ids)
def test_synquid_dependent_applications_typecheck(arity, offset, lower, binder_id):
    context = built_std_context()
    domain = RefinedType(Name("v", 0), t_int, liquid(">=", LiquidVar(Name("v", 0)), LiquidLiteralInt(lower)))
    actuals = [Name(f"x{i}", binder_id + i) for i in range(arity)]
    formals = [Name(f"a{i}", binder_id + arity + i) for i in range(arity)]
    for name in actuals:
        context = context.with_var(name, domain)

    def result(names, amount):
        expression = LiquidVar(names[0])
        for name in names[1:]:
            expression = liquid("+", expression, LiquidVar(name))
        return exact(t_int, liquid("+", expression, LiquidLiteralInt(amount)))

    for component, amount in (("combine", offset), ("distractor", offset + 1)):
        schema = result(formals, amount)
        for name in reversed(formals):
            schema = AbstractionType(name, domain, schema)
        context = context.with_var(Name(component, binder_id), schema)
    candidates = sample_and_check(
        context, result(actuals, offset), {"combine", "distractor", *(n.name for n in actuals)}, depth=1
    )
    assert all(isinstance(term, Application) for term in candidates)


@settings(deadline=None)
@given(arity=st.integers(1, 3), selected=st.integers(0, 2), lower=integers, binder_id=binder_ids)
def test_synquid_dependent_functions_typecheck(arity, selected, lower, binder_id):
    parameters = [Name(f"arg{i}", binder_id + i) for i in range(arity)]
    domain = RefinedType(Name("v", 0), t_int, liquid(">=", LiquidVar(Name("v", 0)), LiquidLiteralInt(lower)))
    goal = exact(t_int, LiquidVar(parameters[selected % arity]))
    for parameter in reversed(parameters):
        goal = AbstractionType(parameter, domain, goal)
    candidates = sample_and_check(built_std_context(), goal, {n.name for n in parameters}, limit=1)
    assert isinstance(candidates[0], Abstraction)


@settings(deadline=None)
@given(arity=st.integers(1, 3), binder_id=binder_ids)
def test_synquid_polymorphic_functions_typecheck(arity, binder_id):
    a = Name("a", binder_id)
    parameters = [Name(f"arg{i}", binder_id + i + 1) for i in range(arity)]
    goal = TypeVar(a)
    for parameter in reversed(parameters):
        goal = AbstractionType(parameter, TypeVar(a), goal)
    goal = TypePolymorphism(a, Kind.BASE, goal)
    candidates = sample_and_check(built_std_context(), goal, {n.name for n in parameters}, limit=arity)
    assert all(isinstance(term, TypeAbstraction) for term in candidates)


@pytest.mark.parametrize("base", [t_int, t_bool], ids=["integer", "boolean"])
@settings(deadline=None)
@given(binder_id=binder_ids)
def test_synquid_polymorphic_applications_typecheck(base, binder_id):
    x, a, arg = Name("x", binder_id), Name("a", binder_id + 1), Name("arg", binder_id + 2)
    identity = TypePolymorphism(a, Kind.BASE, AbstractionType(arg, TypeVar(a), TypeVar(a)))
    context = built_std_context().with_var(x, base).with_var(Name("identity", binder_id), identity)
    goal = exact(base, LiquidVar(x))
    candidates = sample_and_check(context, goal, {"x", "identity"}, depth=1)
    assert any(isinstance(term, Application) and isinstance(term.fun, TypeApplication) for term in candidates)


@settings(deadline=None)
@given(left=integers, gap=st.integers(1, 5), binder_id=binder_ids)
def test_synquid_conditional_candidates_typecheck(left, gap, binder_id):
    b, first, second = (Name(n, binder_id + i) for i, n in enumerate(("b", "first", "second")))
    context = built_std_context().with_var(b, t_bool)
    context = context.with_var(first, exact(t_int, LiquidLiteralInt(left)))
    context = context.with_var(second, exact(t_int, LiquidLiteralInt(left + gap)))
    v = LiquidVar(Name("result", 0))
    goal = RefinedType(
        v.name,
        t_int,
        liquid(
            "||",
            liquid("&&", LiquidVar(b), liquid("==", v, LiquidLiteralInt(left))),
            liquid("&&", liquid("!", LiquidVar(b)), liquid("==", v, LiquidLiteralInt(left + gap))),
        ),
    )
    candidates = sample_and_check(context, goal, {"b", "first", "second"}, conditionals=True, limit=2)
    assert all(isinstance(term, Annotation) and isinstance(term.expr, If) for term in candidates)
