"""Array reads retain their logical definitions in synthesis hole contexts."""

import pytest

from aeon.core.terms import Literal
from aeon.core.types import top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.modules.native_search import initial_partial
from aeon.synthesis.modules.tdsyn.constraints import candidate_feasible
from aeon.synthesis.modules.tdsyn.smt_solve import solve_literals
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import ReflectedBinder


def _driver(source):
    driver = AeonDriver(AeonConfig("tdsyn_backward", SilentSynthesisUI(), 10))
    assert not driver.parse(aeon_code=source)
    assert driver.has_synth()
    return driver


def _hole(driver, name="result"):
    info = get_holes_info(driver.typing_ctx, driver.core, top, driver.incomplete_functions, refined_types=True)
    goal, ctx = next(value for key, value in info.items() if key.name == name)
    return initial_partial(ctx, goal).holes[0]


@pytest.mark.parametrize(
    "element,values,expected",
    [
        ("Int", "3, 7", 7),
        ("Bool", "false, true", True),
        ("Float", "1.5, 2.5", 2.5),
    ],
)
def test_scalar_completion_uses_concrete_array_contents(element, values, expected):
    driver = _driver(f"""
        import Array;
        def data (_:Unit):{{a:(Array {element}) | Array.size a = 2}} := #[{values}];
        def main (u:Int):{{v:{element} | v = Array.get (data unit) 1}} := ?result;
    """)
    with driver.session.activate():
        hole = _hole(driver)
        solutions = solve_literals([hole])
        assert solutions
        assert all(solution[hole.name].value == expected for solution in solutions)
        wrong = False if element == "Bool" else 0 if element == "Int" else 0.0
        assert not candidate_feasible(hole, Literal(wrong, hole.expected_type.type), [])
    driver.synth()
    assert driver.run() == expected


def test_symbolic_index_is_constrained_by_array_contents():
    driver = _driver("""
        import Array;
        def data (_:Unit):{a:(Array Int) | Array.size a = 3} := #[3, 7, 11];
        def main (u:Int):{i:Int | 0 <= i && i < 3 && Array.get (data unit) i = 7} := ?result;
    """)
    with driver.session.activate():
        hole = _hole(driver)
        solutions = solve_literals([hole])
        assert solutions
        assert all(solution[hole.name].value == 1 for solution in solutions)
    driver.synth()
    assert driver.run() == 1


def test_reflection_preserves_polymorphic_executable_signatures():
    driver = _driver("""
        import Array;
        def main (u:Int):Int := ?result;
    """)
    from aeon.core.types import TypePolymorphism

    with driver.session.activate():
        hole = _hole(driver)
        get = next(e for e in hole.context.entries if isinstance(e, ReflectedBinder) and e.name.name == "Array_get")
        assert isinstance(get.type, TypePolymorphism)
        assert (get.name, get.type) in hole.context.concrete_vars()


def test_incomplete_definition_is_not_reflected_into_later_holes():
    driver = _driver("""
        def unknown (x:Int):Int := ?body;
        def main (u:Int):Int := ?result;
    """)
    with driver.session.activate():
        hole = _hole(driver)
        assert not any(isinstance(e, ReflectedBinder) and e.name.name == "unknown" for e in hole.context.entries)


def test_shadowed_array_get_uses_its_actual_definition():
    driver = _driver("""
        def Array_get (x:Int) (i:Int):Int := 19;
        def main (u:Int):{v:Int | v = Array_get 0 1} := ?result;
    """)
    with driver.session.activate():
        hole = _hole(driver)
        solutions = solve_literals([hole])
        assert solutions
        assert all(solution[hole.name].value == 19 for solution in solutions)


def test_closing_empty_preserves_its_weight_equation_for_boolean_siblings():
    from aeon.synthesis.modules.tdsyn.actions import backward_app_candidates, backward_close_candidates
    from aeon.synthesis.modules.tdsyn.smt_solve import all_leaf_holes
    from aeon.synthesis.modules.tdsyn.worklist import PartialAST, expand_at_hole
    from aeon.core.terms import Hole
    from tests.tdsyn_relations_test import MASK, _head

    driver = _driver(
        MASK
        + """
        def main (u:Int):{m:Mask{|fun w => fun rest => w + rest <= 0|} |
            Mask.count m = 2 && Mask.weight m = 0} := ?result;
    """
    )
    with driver.session.activate():
        hole = _hole(driver)
        partial = PartialAST(Hole(hole.name), [hole], 0)
        for _ in range(2):
            tail = next(h for h in partial.holes if not all_leaf_holes([h]))
            term, children = next(
                (t, children)
                for t, children in backward_app_candidates(tail, lambda _: False)
                if _head(t) == "Mask_cons"
            )
            partial = expand_at_hole(partial, tail, term, children, partial.depth + 1)
        tail = next(h for h in partial.holes if not all_leaf_holes([h]))
        term, children = next(
            (t, children)
            for t, children in backward_close_candidates(tail, lambda _: False)
            if _head(t) == "Mask_empty"
        )
        partial = expand_at_hole(partial, tail, term, children, partial.depth)
        solutions = solve_literals(partial.holes)
        assert solutions
        assert all(value.value is False for solution in solutions for value in solution.values())


def test_constructor_bindings_preserve_value_and_refinement_type():
    from aeon.core.substitutions import substitution
    from aeon.core.terms import Application, Let
    from aeon.core.types import t_bool
    from aeon.synthesis.modules.tdsyn.helpers import bind_constructor_arguments, monomorphize
    from aeon.typechecking.typeinfer import check_type
    from tests.tdsyn_relations_test import MASK

    driver = _driver(
        MASK
        + """
        def main (u:Int):{m:Mask{|fun w => fun rest => w + rest <= 0|} |
            Mask.count m = 3 && Mask.weight m = 0} := ?result;
    """
    )
    with driver.session.activate():
        hole = _hole(driver)
        constructors = {
            name.name: monomorphize(name, ty, hole.context, hole.expected_type)[0][0]
            for name, ty in hole.context.vars()
            if name.name in ("Mask_empty", "Mask_cons")
        }
        term = constructors["Mask_empty"]
        for _ in range(3):
            term = Application(Application(constructors["Mask_cons"], term), Literal(False, t_bool))
        shared = bind_constructor_arguments(term)
        assert isinstance(shared, Let)
        assert check_type(hole.context, term, hole.expected_type)
        assert check_type(hole.context, shared, hole.expected_type)
        original = driver.core
        _, [target] = driver.incomplete_functions[0]
        driver.core = substitution(original, term, target)
        expected = driver.run()
        driver.core = substitution(original, shared, target)
        assert driver.run() == expected


def test_constructor_bindings_leave_effectful_fields_in_order():
    from aeon.core.terms import Application, Var
    from aeon.core.types import t_bool, t_unit
    from aeon.synthesis.modules.tdsyn.helpers import bind_constructor_arguments, monomorphize
    from aeon.utils.name import Name
    from tests.tdsyn_relations_test import MASK

    driver = _driver(MASK + "def main (u:Int):Mask := ?result;")
    with driver.session.activate():
        hole = _hole(driver)
        name, ty = next((n, t) for n, t in hole.context.vars() if n.name == "Mask_cons")
        constructor = monomorphize(name, ty, hole.context, hole.expected_type)[0][0]
        effect = Application(Var(Name("effect")), Literal(None, t_unit))
        term = Application(Application(constructor, effect), Literal(False, t_bool))
        assert bind_constructor_arguments(term) == term


def test_constructor_bindings_preserve_curried_call_order():
    from aeon.backend.evaluator import EvaluationContext, eval
    from aeon.core.terms import Application, Var
    from aeon.core.types import t_int
    from aeon.synthesis.modules.tdsyn.helpers import bind_constructor_arguments

    driver = _driver("""
        inductive Chain | end:Chain | node (head:Int) (tail:Chain):Chain
        def main (u:Int):Chain := ?result;
    """)
    with driver.session.activate():
        names = {n.name: n for n, _ in _hole(driver).context.vars()}
        node, end = names["Chain_node"], names["Chain_end"]
        term = Application(Var(node), Literal(2, t_int))
        term = Application(term, Var(end))
        term = Application(Application(Var(node), Literal(1, t_int)), term)
        shared = bind_constructor_arguments(term)
        events = []

        def constructor(head):
            events.append(("head", head))

            def finish(tail):
                events.append(("tail", head))
                return (head, tail)

            return finish

        # Shadow the constructor's runtime implementation to make its curried
        # evaluation observable; hoisting must still preserve that order.
        ctx = EvaluationContext({node: constructor, end: ()})
        expected = eval(term, ctx)
        expected_events = list(events)
        events.clear()
        assert eval(shared, ctx) == expected
        assert events == expected_events
