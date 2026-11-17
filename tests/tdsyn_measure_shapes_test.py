"""Measure-driven structures retain element contracts and ordinary search."""

from dataclasses import replace
from time import monotonic

import pytest
from hypothesis import given, settings, strategies as st
import z3

from aeon.core.substitutions import substitution
from aeon.core.terms import Hole, Literal
from aeon.core.types import t_bool, t_int
from aeon.synthesis.grammar.nonterminals import ExpressionDomain
from aeon.synthesis.modules.tdsyn.constraints import candidate_feasible, deadline
from aeon.synthesis.modules.tdsyn.measure_shapes import measure_shape_candidates, goal_measures, fixed_measure
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, expand_at_hole, locate_holes, substitute_holes_map
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.typeinfer import check_type
from tests.tdsyn_arrays_test import _driver, _hole


def chain_source(datatype="Chain", measure="extent", constructor="link", size=10):
    return f"""
        inductive {datatype}
        | end:{{c:{datatype}|{datatype}.{measure} c=0}}
        | {constructor} (head:{{v:Int|v>=5 && v<=10}})(tail:{datatype}):
            {{c:{datatype}|{datatype}.{measure} c=1+{datatype}.{measure} tail}}
        + {measure}(c:{datatype}):Int
        def main(u:Int):{{c:{datatype}|{datatype}.{measure} c={size}}}:=?result;
    """


@pytest.mark.parametrize("datatype,measure,constructor", [("Chain", "extent", "link"), ("Parcel", "mass", "attach")])
@pytest.mark.parametrize("size", [0, 1, 10])
def test_custom_datatypes_and_measures_need_no_name_recognition(datatype, measure, constructor, size):
    driver = _driver(chain_source(datatype, measure, constructor, size))
    with driver.session.activate():
        hole = _hole(driver)
        [(term, holes)] = measure_shape_candidates(hole, lambda n: n.name == "main")
        assert len(holes) == size
        assert all(not candidate_feasible(h, Literal(4, t_int), []) for h in holes)
        models = solve_literals(holes) if holes else [{}]
        assert models
        candidate = substitute_holes_map(term, models[0])
        assert check_type(hole.context, candidate, hole.expected_type)
        value = execute(driver, candidate)
        count = 0
        while value[0] == f"{datatype}_{constructor}":
            _, head, value = value
            assert 5 <= head <= 10
            count += 1
        assert value == (f"{datatype}_end",)
        assert count == size


@settings(max_examples=8, deadline=None)
@given(st.lists(st.integers(min_value=5, max_value=10), min_size=0, max_size=10))
def test_custom_chain_preserves_arbitrary_payloads_and_order(values):
    driver = _driver(chain_source(size=len(values)))
    with driver.session.activate():
        hole = _hole(driver)
        [(term, holes)] = measure_shape_candidates(hole, lambda n: n.name == "main")
        candidate = substitute_holes_map(term, {h.name: Literal(v, t_int) for h, v in zip(holes, values)})
        assert check_type(hole.context, candidate, hole.expected_type)
        result = execute(driver, candidate)
        observed = []
        while result[0] == "Chain_link":
            _, head, result = result
            observed.append(head)
        assert observed == values


def test_standard_list_uses_the_same_planner():
    driver = _driver("""
        import List;
        def main(u:Int):{l:(List {v:Int|v>=5 && v<=10})|List.size l=10}:=?result;
    """)
    with driver.session.activate():
        hole = _hole(driver)
        [(term, holes)] = measure_shape_candidates(hole, lambda n: n.name == "main")
        assert len(holes) == 10
        models = solve_literals(holes)
        assert models
        candidate = substitute_holes_map(term, models[0])
        assert check_type(hole.context, candidate, hole.expected_type)


def test_branching_measure_offers_a_valid_shape_without_removing_alternatives():
    driver = _driver("""
        inductive Tree
        | leaf (value:Int):{t:Tree|Tree.nodes t=1}
        | branch(left:Tree)(right:Tree):{t:Tree|Tree.nodes t=1+Tree.nodes left+Tree.nodes right}
        + nodes(t:Tree):Int
        def main(u:Int):{t:Tree|Tree.nodes t=7}:=?result;
    """)
    with driver.session.activate():
        hole = _hole(driver)

        def skip(n):
            return n.name == "main"

        [(term, holes)] = measure_shape_candidates(hole, skip)
        assert len(holes) == 4
        models = solve_literals(holes)
        assert models
        assert check_type(hole.context, substitute_holes_map(term, models[0]), hole.expected_type)
        partial = PartialAST(Hole(hole.name), [hole], 0)
        expansions = list(TDSynSynthesizer()._iter_expansions(partial, hole, skip))
        # The normal single-node production still leaves two structural holes.
        assert any(
            len(p.holes) == 2 and all(str(h.expected_type).startswith("Tree") for h in p.holes) for p in expansions
        )


def test_relational_constructor_payload_contract_survives_planning():
    from tests.tdsyn_relations_test import MASK

    driver = _driver(
        MASK
        + """
        def main(u:Int):{m:Mask{|fun w => fun rest => w+rest<=1|}|
            Mask.count m=3 && Mask.weight m=1}:=?result;
    """
    )
    with driver.session.activate():
        hole = _hole(driver)
        [(term, holes)] = measure_shape_candidates(hole, lambda n: n.name == "main")
        assert len(holes) == 3
        models = solve_literals(holes)
        assert models
        for model in models[:2]:
            assert check_type(hole.context, substitute_holes_map(term, model), hole.expected_type)
        invalid = substitute_holes_map(term, {h.name: Literal(True, t_bool) for h in holes})
        assert not check_type(hole.context, invalid, hole.expected_type)


def test_scalar_dependent_measure_does_not_become_a_structural_template():
    driver = _driver("""
        inductive Payload
        | mk(value:Int):{p:Payload|Payload.mass p=value}
        + mass(p:Payload):Int
        def main(u:Int):{p:Payload|Payload.mass p=10}:=?result;
    """)
    with driver.session.activate():
        assert measure_shape_candidates(_hole(driver), lambda n: n.name == "main") == []


def test_equal_measure_cycles_cannot_build_a_shape_without_a_base():
    from aeon.synthesis.modules.tdsyn.measure_shapes import _plan, _productions

    driver = problem("10")
    with driver.session.activate():
        hole = _hole(driver)
        measure = next(goal_measures(hole))
        # Array reverse/set/map have zero offset and one same-rank child.
        productions = [p for p in _productions(hole, lambda n: n.name == "main", measure) if p.children]
        assert _plan(productions, 10) is None


@pytest.mark.parametrize("backend", ["tdsyn_enumerative", "tdsyn_backward", "tdsyn_random"])
@pytest.mark.parametrize("datatype", ["list", "chain", "tree"])
def test_driver_completes_measured_datatypes_with_element_contracts(backend, datatype):
    from aeon.facade.driver import AeonConfig, AeonDriver

    sources = {
        "list": """
            import List;
            def main(u:Int):{l:(List {v:Int|v>=5 && v<=10})|List.size l=10}:=?result;
        """,
        "chain": chain_source(),
        "tree": """
            inductive Tree
            | leaf(value:{v:Int|v>=5 && v<=10}):{t:Tree|Tree.nodes t=1}
            | branch(left:Tree)(right:Tree):{t:Tree|Tree.nodes t=1+Tree.nodes left+Tree.nodes right}
            + nodes(t:Tree):Int
            def main(u:Int):{t:Tree|Tree.nodes t=7}:=?result;
        """,
    }
    # Use the real driver: the linked sketch supplies ownership information
    # about reusable ADT constructors that a bare check_type callback lacks.
    driver = AeonDriver(AeonConfig(backend, SilentSynthesisUI(), 15, tdsyn_expansion="lazy"))
    assert not driver.parse(aeon_code=sources[datatype])
    assert driver.has_synth()
    driver.synth()
    value = driver.run()
    if datatype == "tree":

        def count(tree):
            if tree[0] == "Tree_leaf":
                assert 5 <= tree[1] <= 10
                return 1
            return 1 + count(tree[1]) + count(tree[2])

        assert count(value) == 7
    else:
        prefix, constructor, end = ("List", "cons", "nil") if datatype == "list" else ("Chain", "link", "end")
        elements = []
        while value[0] == f"{prefix}_{constructor}":
            _, head, value = value
            elements.append(head)
        assert value == (f"{prefix}_{end}",)
        assert len(elements) == 10 and all(5 <= v <= 10 for v in elements)


def goal_rank(hole):
    return next((fixed_measure(hole, m) for m in goal_measures(hole)), None)


def problem(size="10", element="Bool", arguments="u:Int"):
    return _driver(f"""
        import Array;
        def main ({arguments}):{{a:(Array {element}) | Array.size a = {size}}} := ?result;
    """)


def execute(driver, candidate):
    original = driver.core
    target = driver.incomplete_functions[0][1][0]
    try:
        driver.core = substitution(original, candidate, target)
        return driver.run()
    finally:
        driver.core = original


@pytest.mark.parametrize("size", [0, 1, 2, 10, 50])
def test_shape_has_exactly_one_boolean_hole_per_element(size):
    driver = problem(str(size))
    with driver.session.activate():
        hole = _hole(driver)
        assert goal_rank(hole) == size
        [(term, holes)] = measure_shape_candidates(hole, lambda n: n.name in {"main", "build"})
        assert len(holes) == len(locate_holes(term)) == size
        initial = PartialAST(Hole(hole.name), [hole], 0, expected_type=hole.expected_type, context=hole.context)
        partial = expand_at_hole(initial, hole, term, holes, 1)
        assert partial.qtt_feasible()
        models = solve_literals(holes) if holes else [{}]
        assert models
        for model in models[:2]:
            result = substitute_holes_map(term, model)
            assert check_type(hole.context, result, hole.expected_type)
            values = execute(driver, result)
            assert len(values) == size and all(type(v) is bool for v in values)


@settings(max_examples=12, deadline=None)
@given(st.lists(st.booleans(), min_size=1, max_size=16))
def test_shape_preserves_element_order_for_arbitrary_assignments(values):
    driver = problem(str(len(values)))
    with driver.session.activate():
        hole = _hole(driver)
        [(term, holes)] = measure_shape_candidates(hole, lambda n: n.name in {"main", "build"})
        assignment = {h.name: Literal(v, t_bool) for h, v in zip(holes, values)}
        candidate = substitute_holes_map(term, assignment)
        assert check_type(hole.context, candidate, hole.expected_type)
        assert execute(driver, candidate) == values


def test_every_numeric_element_retains_its_refinement():
    driver = problem(element="{x:Int | x >= 5 && x <= 10}")
    with driver.session.activate():
        hole = _hole(driver)
        [(term, holes)] = measure_shape_candidates(hole, lambda n: n.name in {"main", "build"})
        assert len(holes) == 10
        assert all(not candidate_feasible(h, Literal(4, t_int), []) for h in holes)
        models = solve_literals(holes)
        assert models
        for model in models[:2]:
            candidate = substitute_holes_map(term, model)
            assert check_type(hole.context, candidate, hole.expected_type)
            values = execute(driver, candidate)
            assert len(values) == 10 and all(5 <= value <= 10 for value in values)


def test_array_content_constraints_reach_the_element_holes():
    driver = _driver("""
        import Array;
        def main(u:Int):{a:(Array Int) | Array.size a = 10 && Array.get a 9 = 7} := ?result;
    """)
    with driver.session.activate():
        hole = _hole(driver)
        [(term, holes)] = measure_shape_candidates(hole, lambda n: n.name in {"main", "build"})
        models = solve_literals(holes)
        assert models
        for model in models[:2]:
            candidate = substitute_holes_map(term, model)
            assert check_type(hole.context, candidate, hole.expected_type)
            assert execute(driver, candidate)[9] == 7


@pytest.mark.parametrize("size,arguments", [("5 + 5", "u:Int"), ("n", "n:{v:Int | v = 10}")])
def test_length_is_proved_from_arithmetic_and_context(size, arguments):
    driver = _driver(f"""
        import Array;
        def build ({arguments}):{{a:(Array Bool) | Array.size a = {size}}} := ?result;
        def main(u:Int):(Array Bool) := build 10;
    """)
    with driver.session.activate():
        assert goal_rank(_hole(driver)) == 10


@pytest.mark.parametrize(
    "predicate",
    [
        "true",
        "Array.size a >= 5 && Array.size a <= 10",
        "Array.size a = (0 - 1)",
        "Array.size a = 257",
        "Array.size a = 3 && Array.size a = 4",
    ],
)
def test_ambiguous_impossible_and_oversized_goals_keep_ordinary_search(predicate):
    driver = _driver(f"import Array; def main(u:Int):{{a:(Array Bool) | {predicate}}} := ?result;")
    with driver.session.activate():
        hole = _hole(driver)
        assert goal_rank(hole) is None
        assert measure_shape_candidates(hole, lambda n: n.name in {"main", "build"}) == []


def test_smt_unknown_and_expired_budget_do_not_guess_a_shape(monkeypatch):
    driver = problem()
    with driver.session.activate():
        hole = _hole(driver)
        with monkeypatch.context() as patch:
            patch.setattr(z3.Solver, "check", lambda *args: z3.unknown)
            assert goal_rank(hole) is None
        token = deadline.set(monotonic() - 1)
        try:
            assert goal_rank(hole) is None
        finally:
            deadline.reset(token)
        assert goal_rank(hole) == 10


def test_refinement_expression_holes_are_not_runtime_arrays():
    driver = problem()
    with driver.session.activate():
        assert (
            measure_shape_candidates(
                replace(_hole(driver), domain=ExpressionDomain.REFINEMENT), lambda n: n.name in {"main", "build"}
            )
            == []
        )


@pytest.mark.parametrize("excluded", ["all", "Array_mk_concat", "Array_mk_32", "Array_mk_1"])
def test_constructor_skip_rules_are_respected(excluded):
    driver = problem("50")
    with driver.session.activate():
        hole = _hole(driver)
        candidates = measure_shape_candidates(
            hole, lambda n: n.name == "main" or excluded == "all" or n.name == excluded
        )
        if excluded in ("all", "Array_mk_concat"):
            assert candidates == []
        else:
            [(term, holes)] = candidates
            assert len(holes) == 50
            if excluded == "Array_mk_32":
                assert "Array_mk_32" not in str(term)


@pytest.mark.parametrize("expansion", ["eager", "lazy"])
@pytest.mark.parametrize("mode,direction", [("enumerative", "both"), ("enumerative", "backward"), ("random", "both")])
def test_search_modes_can_complete_the_fixed_array_shape(expansion, mode, direction):
    driver = problem(element="{x:Int | x >= 5 && x <= 10}")
    with driver.session.activate():
        hole = _hole(driver)
        backend = TDSynSynthesizer(mode=mode, direction=direction, expansion=expansion)
        result = backend.synthesize(
            hole.context,
            hole.expected_type,
            lambda term: check_type(hole.context, term, hole.expected_type),
            lambda _: [],
            driver.incomplete_functions[0][0],
            {},
            budget=10,
            ui=SilentSynthesisUI(),
        )
        values = execute(driver, result)
        assert len(values) == 10 and all(5 <= value <= 10 for value in values)


@pytest.mark.parametrize("expansion", ["eager", "lazy"])
def test_fixed_shape_is_offered_before_ordinary_array_expressions(expansion):
    driver = problem("50")
    with driver.session.activate():
        hole = _hole(driver)
        partial = PartialAST(Hole(hole.name), [hole], 0, expected_type=hole.expected_type, context=hole.context)
        backend = TDSynSynthesizer(expansion=expansion)
        candidates = backend._iter_expansions if expansion == "lazy" else backend._expand_hole
        first = next(iter(candidates(partial, hole, lambda n: n.name in {"main", "build"})))
        assert len(first.holes) == 50


@pytest.mark.parametrize("expansion", ["eager", "lazy"])
def test_fixed_shape_can_be_disabled_for_comparisons(monkeypatch, expansion):
    from aeon.synthesis.modules.tdsyn import synthesizer

    def forbidden(*args):
        pytest.fail("Disabled introduction rule was invoked")

    driver = problem("2")
    with driver.session.activate():
        hole = _hole(driver)
        monkeypatch.setattr(synthesizer, "measure_shape_candidates", forbidden)
        monkeypatch.setattr(synthesizer, "iter_measure_shape_candidates", forbidden)
        partial = PartialAST(Hole(hole.name), [hole], 0)
        backend = TDSynSynthesizer(expansion=expansion, measure_shapes=False)
        candidates = backend._iter_expansions if expansion == "lazy" else backend._expand_hole
        assert next(iter(candidates(partial, hole, lambda n: n.name in {"main", "build"})), None) is not None
