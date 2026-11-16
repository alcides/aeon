"""An expanded expression must remain connected to its parent value witness."""

import operator

import pytest
from hypothesis import given, settings, strategies as st

from aeon.compilation.session import CompilationSession
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.parser import parse_type
from aeon.core.terms import Hole, Literal
from aeon.core.types import RefinedType, t_bool, t_int
from aeon.synthesis.modules.native_search import initial_partial
from aeon.synthesis.modules.tdsyn.actions import (
    backward_app_candidates,
    backward_if_candidates,
    iter_backward_app_candidates,
)
from aeon.synthesis.modules.tdsyn.constraints import candidate_feasible, eager_pruning
from aeon.synthesis.modules.tdsyn.helpers import base_type_of
from aeon.synthesis.modules.tdsyn.library import clear_component_library_cache
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, expand_at_hole, substitute_holes_map
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name


def expand_operator(partial, hole, op, *, lazy=False):
    # Production search keeps its skip filter stable; these focused expansions
    # change the filter between operators in the same context.
    clear_component_library_cache()

    def skip(name):
        return name != Name(op, 0)

    candidates = iter_backward_app_candidates(hole, skip) if lazy else backward_app_candidates(hole, skip)
    [(term, children)] = [
        (term, children)
        for term, children in candidates
        if all(base_type_of(child.expected_type) == t_int for child in children)
    ]
    expanded = expand_at_hole(partial, hole, term, children, partial.depth + 1)
    return expanded, [next(h for h in expanded.holes if h.name == c.name) for c in children]


@pytest.mark.parametrize("lazy", [False, True])
@pytest.mark.parametrize(
    "op,goal,evaluate",
    [
        ("+", "{v:Int | v == 50}", lambda x, y: x + y == 50),
        ("-", "{v:Int | v == 50}", lambda x, y: x - y == 50),
        ("*", "{v:Int | v == 50}", lambda x, y: x * y == 50),
        ("==", "{v:Bool | v}", operator.eq),
        ("!=", "{v:Bool | v}", operator.ne),
        ("<", "{v:Bool | v}", operator.lt),
        ("<=", "{v:Bool | v}", operator.le),
        (">", "{v:Bool | v}", operator.gt),
        (">=", "{v:Bool | v}", operator.ge),
    ],
)
def test_operator_models_obey_the_parent_goal(lazy, op, goal, evaluate):
    with CompilationSession().activate():
        partial = initial_partial(built_std_context(), parse_type(goal))
        expanded, [left, right] = expand_operator(partial, partial.holes[0], op, lazy=lazy)
        solutions = solve_literals(expanded.holes)
        assert solutions
        for solution in solutions:
            assert evaluate(solution[left.name].value, solution[right.name].value)
            term = substitute_holes_map(expanded.term, solution)
            assert check_type(partial.context, term, partial.expected_type)


@settings(max_examples=25, deadline=None)
@given(target=st.integers(-50, 50), first=st.integers(-20, 20))
def test_fixing_one_leaf_constrains_its_sibling_and_keeps_other_branches(target, first):
    with CompilationSession().activate():
        value = Name("v", 800)
        goal = RefinedType(value, t_int, LiquidApp(Name("==", 0), [LiquidVar(value), LiquidLiteralInt(target)]))
        partial = initial_partial(built_std_context(), goal)
        expanded, [left, right] = expand_operator(partial, partial.holes[0], "+")
        chosen = expand_at_hole(expanded, left, Literal(first, t_int), [], 2)
        [remaining] = chosen.holes
        assert not candidate_feasible(remaining, Literal(target - first + 1, t_int), [])
        assert candidate_feasible(remaining, Literal(target - first, t_int), [])
        solutions = solve_literals(chosen.holes)
        assert solutions and all(s[right.name].value == target - first for s in solutions)
        # Installing a leaf in one branch does not mutate a sibling branch.
        assert candidate_feasible(left, Literal(first + 1, t_int), [])


def test_constraints_reach_leaves_through_multiple_expansions():
    with CompilationSession().activate():
        partial = initial_partial(built_std_context(), parse_type("{v:Int | v == 50}"))
        expanded, [left, right] = expand_operator(partial, partial.holes[0], "+")
        expanded = expand_at_hole(expanded, right, Literal(30, t_int), [], 2)
        [left] = expanded.holes
        expanded, [a, b] = expand_operator(expanded, left, "-")
        expanded = expand_at_hole(expanded, b, Literal(7, t_int), [], 4)
        [a] = expanded.holes
        assert not candidate_feasible(a, Literal(0, t_int), [])
        solutions = solve_literals(expanded.holes)
        assert solutions and all(s[a.name].value == 27 for s in solutions)


@pytest.mark.parametrize("prune", [False, True])
def test_array_length_equation_reaches_arithmetic_leaves(prune):
    from tests.tdsyn_refined_elements_test import driver_hole

    driver, root = driver_hole("""
        import Array (mk_repeat, size);
        def f (_:Unit):{a:(Array Bool) | Array.size a = 50} := ?result;
    """)
    with driver.session.activate():
        partial = PartialAST(Hole(root.name), [root], 0)
        [(term, children)] = backward_app_candidates(root, lambda n: n.name != "Array_mk_repeat")
        expanded = expand_at_hole(partial, root, term, children, 1)
        size = next(h for h in expanded.holes if base_type_of(h.expected_type) == t_int)
        token = eager_pruning.set(prune)
        try:
            expanded, [left, right] = expand_operator(expanded, size, "+")
            expanded = expand_at_hole(expanded, left, Literal(0, t_int), [], 3)
            solutions = solve_literals(expanded.holes)
        finally:
            eager_pruning.reset(token)
        assert solutions and all(s[right.name].value == 50 for s in solutions)
        pending = next(h for h in expanded.holes if h.name == right.name)
        assert not candidate_feasible(pending, Literal(4, t_int), [])
        assert candidate_feasible(pending, Literal(50, t_int), [])
        for solution in solutions:
            candidate = substitute_holes_map(expanded.term, solution)
            assert check_type(root.context, candidate, root.expected_type)


def test_arithmetic_equations_remain_guarded_in_inactive_branch():
    with CompilationSession().activate():
        partial = initial_partial(built_std_context(), parse_type("{v:Int | v == 50}"))
        root = partial.holes[0]
        [(term, children)] = backward_if_candidates(root, lambda _: False)
        expanded = expand_at_hole(partial, root, term, children, 1)
        condition, then, otherwise = expanded.holes
        expanded = expand_at_hole(expanded, condition, Literal(False, t_bool), [], 2)
        otherwise = next(h for h in expanded.holes if h.name == otherwise.name)
        expanded = expand_at_hole(expanded, otherwise, Literal(50, t_int), [], 3)
        [then] = expanded.holes
        expanded, [a, b] = expand_operator(expanded, then, "+")
        expanded = expand_at_hole(expanded, a, Literal(0, t_int), [], 5)
        [b] = expanded.holes
        assert candidate_feasible(b, Literal(4, t_int), [])


def test_opaque_polymorphic_function_keeps_its_contract_without_a_fake_smt_application():
    with CompilationSession().activate():
        f = Name("opaque", 900)
        ctx = built_std_context().with_var(f, parse_type("forall a:B, (x:Int) -> {v:Int | v == x}"))
        partial = initial_partial(ctx, parse_type("{v:Int | v == 50}"))
        term, children = backward_app_candidates(partial.holes[0], lambda n: n != f)[0]
        expanded = expand_at_hole(partial, partial.holes[0], term, children, 1)
        solutions = solve_literals(expanded.holes)
        assert solutions and all(s[children[0].name].value == 50 for s in solutions)
