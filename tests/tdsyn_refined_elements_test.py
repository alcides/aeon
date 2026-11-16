"""Refined collection elements and dependent signatures in every tactic."""

import pytest
from hypothesis import given, settings, strategies as st

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar, liquid_free_vars
from dataclasses import replace

from aeon.core.terms import Application, Hole, Literal, Rec, Var
from aeon.core.types import (
    AbstractionType,
    Kind,
    RefinedType,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    t_bool,
    t_int,
    t_unit,
    top,
    type_free_term_vars,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.modules.native_search import initial_partial
from aeon.synthesis.modules.tdsyn.actions import _compatible_result, backward_app_candidates
from aeon.synthesis.modules.tdsyn.helpers import get_return_type, monomorphize
from aeon.synthesis.modules.tdsyn.library import get_component_library
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.modules.tdsyn.synthesizer import ONE_STEP_ACTIONS
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, expand_at_hole, fresh_hole, substitute_holes_map
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.tactics.builtin import tactic_constructor
from aeon.synthesis.tactics.holes import collect_hole_judgments
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.typechecking.linearity import check_linearity
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name


def app(operator, *args):
    return LiquidApp(Name(operator, 0), list(args))


def bounded(lo=5, hi=10):
    v = Name("element", 700)
    return RefinedType(
        v,
        t_int,
        app("&&", app("<=", LiquidLiteralInt(lo), LiquidVar(v)), app("<=", LiquidVar(v), LiquidLiteralInt(hi))),
    )


@settings(max_examples=30, deadline=None)
@given(depth=st.integers(1, 4), binder=st.integers(1, 10000), lo=st.integers(-20, 20))
def test_open_nested_result_shape_never_queries_smt(depth, binder, lo):
    value, element = Name("argument", binder), Name("x", binder + 1)
    actual = RefinedType(element, t_int, app("==", LiquidVar(element), LiquidVar(value)))
    goal, wrong = bounded(lo, lo + 5), t_bool
    for _ in range(depth):
        actual = TypeConstructor(Name("Container"), [actual])
        goal = TypeConstructor(Name("Container"), [goal])
        wrong = TypeConstructor(Name("Container"), [wrong])
    # There is deliberately no declaration for the signature's argument.
    assert _compatible_result(TypingContext(), actual, goal)
    assert not _compatible_result(TypingContext(), actual, wrong)


def test_goal_specialization_and_cache_preserve_distinct_element_refinements():
    a, x, make, box = Name("a"), Name("x"), Name("make"), Name("Box")
    ty = TypePolymorphism(a, Kind.BASE, AbstractionType(x, TypeVar(a), TypeConstructor(box, [TypeVar(a)])))
    ctx = TypingContext().with_var(make, ty)
    low, high = TypeConstructor(box, [bounded(5, 10)]), TypeConstructor(box, [bounded(20, 30)])

    def skip(_):
        return False

    first = get_component_library(ctx, skip, low)
    second = get_component_library(ctx, skip, high)
    assert first is not second
    assert first is get_component_library(ctx, skip, low)
    assert any(f.var_type == bounded(5, 10) and get_return_type(f) == low for _, f in first.functions)
    assert any(f.var_type == bounded(20, 30) and get_return_type(f) == high for _, f in second.functions)


def test_distinct_polymorphic_parameters_match_their_goal_positions():
    a, b = Name("a"), Name("b")
    pair = Name("Pair")
    schema = TypePolymorphism(
        a, Kind.BASE, TypePolymorphism(b, Kind.BASE, TypeConstructor(pair, [TypeVar(a), TypeVar(b)]))
    )
    goal = TypeConstructor(pair, [bounded(), t_bool])
    assert any(ty == goal for _, ty in monomorphize(Name("pair"), schema, TypingContext(), goal))


def driver_hole(source):
    driver = AeonDriver(AeonConfig("tdsyn_enumerative", SilentSynthesisUI(), 30))
    assert not list(driver.parse(aeon_code=source))
    assert driver.has_synth()
    with driver.session.activate():
        info = get_holes_info(driver.typing_ctx, driver.core, top, driver.incomplete_functions, refined_types=True)
        name = driver.incomplete_functions[0][1][0]
        goal, ctx = info[name]
        return driver, initial_partial(ctx, goal).holes[0]


ARRAY_GOAL = "{xs:(Array {v:Int | 5 <= v && v <= 10}) | Array.size xs = 10}"


def test_repeat_completion_binds_arguments_and_satisfies_element_bounds():
    driver, hole = driver_hole(f"open Array\ndef result (_:Unit) : {ARRAY_GOAL} := ?body;")
    with driver.session.activate():
        candidates = [
            (term, holes) for term, holes in backward_app_candidates(hole, lambda n: n.name != "Array_mk_repeat")
        ]
        assert candidates
        valid = []
        for term, children in candidates:
            for solution in solve_literals(children):
                candidate = substitute_holes_map(term, solution)
                if check_type(hole.context, candidate, hole.expected_type):
                    valid.append(candidate)
                    assert solution[children[0].name].value == 10
                    assert 5 <= solution[children[1].name].value <= 10
        assert valid, "Array repeat must have a bound-respecting completion"


@pytest.mark.parametrize("action", list(ONE_STEP_ACTIONS))
@pytest.mark.parametrize("function_goal", [False, True])
def test_all_tactics_keep_child_types_and_obligations_in_scope(action, function_goal):
    driver, hole = driver_hole(
        f"open Array\ndef result (n:{{v:Int | v = 10}}) (v:{{v:Int | 5 <= v && v <= 10}}) : {ARRAY_GOAL} := ?body;"
    )
    allowed = {"Array_mk_repeat", "n", "v"}
    if function_goal:
        hole = replace(hole, expected_type=AbstractionType(Name("input", 9000), t_unit, hole.expected_type))
    with driver.session.activate():
        candidates = ONE_STEP_ACTIONS[action](hole, lambda n: n.name not in allowed)
        for term, children in candidates:
            witnesses = {h.name for h in children}
            for child in children:
                visible = {n for n, _ in child.context.vars()} | set(child.bindings) | witnesses
                assert set(type_free_term_vars(child.expected_type)) <= visible
                for binding in child.bindings.values():
                    assert set(type_free_term_vars(binding)) <= visible
                for predicate in child.constraints:
                    assert set(liquid_free_vars(predicate)) <= visible
            if isinstance(term, Rec):
                visible = {n for n, _ in hole.context.vars()}
                assert set(type_free_term_vars(term.var_type)) <= visible
        # These application tactics must exercise the regression, not pass
        # vacuously by swallowing the unbound-variable exception.
        if not function_goal and action in ("backward", "backward_app", "forward_let_app", "forward_let_tapp"):
            assert candidates
        if function_goal and action in ("backward", "backward_abs"):
            assert candidates


@settings(max_examples=20, deadline=None)
@given(binder=st.integers(1, 10000), lo=st.integers(-20, 20))
def test_dependent_application_freshens_every_argument_before_checking_contracts(binder, lo):
    x, y, v = [Name(name, binder) for name in ("x", "y", "v")]
    array = Name("Box")
    signature = AbstractionType(
        x,
        bounded(lo, lo + 5),
        AbstractionType(
            y,
            RefinedType(v, t_int, app("==", LiquidVar(v), LiquidVar(x))),
            TypeConstructor(array, [RefinedType(v, t_int, app("==", LiquidVar(v), LiquidVar(y)))]),
        ),
    )
    f = Name("make", binder)
    ctx = built_std_context().with_var(f, signature)
    _, hole = fresh_hole(TypeConstructor(array, [bounded(lo, lo + 5)]), ctx)
    candidates = backward_app_candidates(hole, lambda n: n != f)
    assert len(candidates) == 1
    _, children = candidates[0]
    witnesses = {child.name for child in children}
    for child in children:
        visible = {n for n, _ in ctx.vars()} | witnesses | set(child.bindings)
        assert set(type_free_term_vars(child.expected_type)) <= visible
        for ty in child.bindings.values():
            assert set(type_free_term_vars(ty)) <= visible
        for predicate in child.constraints:
            assert set(liquid_free_vars(predicate)) <= visible
        assert not ({x, y} & visible)

    state = TacticState(ctx, Hole(hole.name), hole.expected_type)
    expanded = tactic_constructor(state, hole.name)
    assert expanded is not None
    judgments = collect_hole_judgments(ctx, expanded.term, expanded.goal)
    assert len(judgments) == 2
    for ty, local in judgments.values():
        visible = {n for n, _ in local.vars()}
        assert set(type_free_term_vars(ty)) <= visible
        assert not ({x, y} & visible)


def test_partial_search_uses_constructor_ownership_from_the_linked_program():
    driver, hole = driver_hole(f"open List\ndef result (_:Unit) : {ARRAY_GOAL.replace('Array', 'List')} := ?body;")
    with driver.session.activate():
        root_name = driver.incomplete_functions[0][1][0]

        def check_sketch(term):
            return not check_linearity(substitute_holes_map(driver.core, {root_name: term}), driver.typing_ctx)

        partial = PartialAST(
            Hole(hole.name),
            [hole],
            0,
            expected_type=hole.expected_type,
            context=hole.context,
            check_sketch=check_sketch,
        )
        # Two nested constructor applications were incorrectly discarded by a
        # second ownership check that could see only their opaque signatures.
        for _ in range(2):
            tail = partial.holes[-1]
            [(term, children)] = backward_app_candidates(tail, lambda n: n.name != "List_cons")
            partial = expand_at_hole(partial, tail, term, children, partial.depth + 1)
        assert not replace(partial, check_sketch=None).qtt_feasible()
        assert partial.qtt_feasible()
        assert TacticState(hole.context, partial.term, hole.expected_type, check_sketch).qtt_feasible()


@pytest.mark.parametrize("expansion", ["eager", "lazy"])
@pytest.mark.parametrize("collection", ["List", "Array"])
def test_synthesis_returns_ten_bounded_numbers(collection, expansion):
    # A small constructor vocabulary makes this a deterministic correctness
    # regression; the separate benchmark uses the entire standard library.
    source = (
        "inductive List a\n"
        "| nil : {xs:(List a) | size xs = 0}\n"
        "| cons (hd:a) (tl:(List a)) : {xs:(List a) | size xs = size tl + 1 && size tl >= 0}\n"
        "+ size (xs:(List a)):Int\n"
        if collection == "List"
        else "import Array (mk_repeat, size);\n"
    )
    source += f"def result (_:Unit) : {ARRAY_GOAL.replace('Array', collection)} := ?body;"
    if collection == "List":
        source = source.replace("List.size", "size")
    driver = AeonDriver(AeonConfig("tdsyn_enumerative", SilentSynthesisUI(), 20, tdsyn_expansion=expansion))
    assert not list(driver.parse(aeon_code=source))
    assert driver.has_synth()
    target = driver.incomplete_functions[0][0]
    driver.synth()  # A timeout is a failure here, not a skipped regression.
    assert not check_linearity(driver.core, driver.typing_ctx)
    from aeon.core.substitutions import substitution

    driver.core = substitution(driver.core, Application(Var(target), Literal(None, t_unit)), Name("main", 0))
    result = driver.run()
    if collection == "List":
        elements = []
        while isinstance(result, tuple) and len(result) == 3 and result[0] == "List_cons":
            elements.append(result[1])
            result = result[2]
        assert result == ("List_nil",)
    else:
        elements = result
    assert len(elements) == 10
    assert all(type(value) is int and 5 <= value <= 10 for value in elements)
