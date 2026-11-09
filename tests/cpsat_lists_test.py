"""CP-SAT constructs fixed-length lists from a single structured hole."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.ortools_cpsat import CPSatHoleSynthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI

pytest.importorskip("ortools")


@pytest.fixture
def symbolic(monkeypatch):
    def no_fallback(*args, **kwargs):
        pytest.fail("fixed list constraints and scoring should translate symbolically")

    monkeypatch.setattr(CPSatHoleSynthesizer, "_runtime_search", no_fallback)


def _driver(source):
    driver = AeonDriver(AeonConfig("ortools", SilentSynthesisUI(), 10))
    assert not driver.parse(aeon_code=source)
    assert driver.has_synth()
    return driver


def _solve(driver):
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    backend = CPSatHoleSynthesizer(bound=10)
    with driver.session.activate():
        mapping = backend.synthesize_program(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            targets,
            driver.metadata,
            budget=5,
            ui=SilentSynthesisUI(),
        )
    return mapping, backend


@pytest.mark.parametrize("size", [0, 1, 4])
@pytest.mark.parametrize(
    "element,score,expected",
    [
        ("Bool", "if h then 1 else 0", True),
        ("Int", "h", 1000),
        ("Float", "h", 1000.0),
    ],
)
def test_standard_list_elements(symbolic, size, element, score, expected):
    numeric = "Float" if "Float" in element else "Int"
    zero = "0.0" if numeric == "Float" else "0"
    objective = "score result" if numeric == "Float" else "toFloat (score result)"
    driver = _driver(f"""
        import List;
        def score (xs:(List {element})):{numeric} :=
            match xs with | nil => {zero} | cons h t => ({score}) + score t;
        @maximize({objective})
        def result: {{xs:(List {element}) | List.size xs = {size}}} := ?xs;
        def main (u:Int): (List {element}) := result;
    """)
    driver.synth()
    value = driver.run()
    elements = []
    while value[0] == "List_cons":
        _, head, value = value
        elements.append(head)
    assert value == ("List_nil",)
    assert elements == [expected] * size


MASK = """
    inductive Mask forall <fits:Int -> Int -> Bool>
    | empty: {m:Mask{|fits|} | Mask.count m = 0 && Mask.weight m = 0}
    | cons (rest:Mask{|fits|}) (used:{b:Bool | fits (if b then 3 else 0) (Mask.weight rest)}):
        {m:Mask{|fits|} | Mask.count m = Mask.count rest + 1 &&
            Mask.weight m = Mask.weight rest + (if used then 3 else 0)}
    + count (m:Mask):Int
    + weight (m:Mask):Int
    def score (m:Mask{|fun w => fun rest => w + rest <= 6|}):Int :=
        match m with | empty => 0 | cons rest used => (if used then 1 else 0) + score rest;
"""


@pytest.mark.parametrize("capacity,expected", [(0, 0), (3, 1), (9, 2)])
def test_relational_tail_first_list_and_result_refinement(symbolic, capacity, expected):
    driver = _driver(
        MASK
        + f"""
        @maximize(toFloat (score result))
        def result: {{m:Mask{{|fun w => fun rest => w + rest <= 6|}} |
            Mask.count m = 3 && Mask.weight m <= {capacity}}} := ?solution;
        def main (u:Int):Int := score result;
    """
    )
    driver.synth()
    assert driver.run() == expected


@pytest.mark.parametrize(
    "refinement",
    [
        "Mask.weight m = 3",
        "Mask.count m <= 3",
        "Mask.count m = 1 || Mask.count m = 3",
    ],
)
def test_length_requires_a_structural_measure_and_positive_equality(refinement):
    driver = _driver(
        MASK
        + f"""
        def result: {{m:Mask{{|fun w => fun rest => w + rest <= 6|}} | {refinement}}} := ?solution;
    """
    )
    with pytest.raises(UnsupportedSynthesisGoal, match="fixed-length list"):
        _solve(driver)


def test_empty_list_still_enforces_other_refinements(symbolic):
    driver = _driver(
        MASK
        + """
        @maximize(toFloat (score result))
        def result: {m:Mask{|fun w => fun rest => w + rest <= 6|} |
            Mask.count m = 0 && Mask.weight m > 0} := ?solution;
    """
    )
    mapping, _ = _solve(driver)
    assert len(mapping) == 1
    assert next(iter(mapping.values())) is None


def test_multiple_lists_and_scalar_keep_original_hole_mapping(symbolic):
    driver = _driver(
        MASK
        + """
        def first: {m:Mask{|fun w => fun rest => w + rest <= 6|} | Mask.count m = 2} := ?a;
        def second: {m:Mask{|fun w => fun rest => w + rest <= 6|} | Mask.count m = 1} := ?b;
        def scalar: {v:Int | 0 <= v && v <= 2} := ?n;
        @maximize(toFloat (score first + score second + scalar))
        def total:Int := score first + score second + scalar;
    """
    )
    mapping, backend = _solve(driver)
    assert {name.name for name in mapping} == {"a", "b", "n"}
    assert all(value is not None for value in mapping.values())
    assert backend.pareto_front[0][0] == [-5.0]
    assert len(backend.pareto_front[0][1].terms) == 3


@pytest.mark.parametrize("element,upper,zero", [("Int", "3", "0"), ("Float", "0.5", "0.0")])
def test_custom_list_preserves_element_bounds(symbolic, element, upper, zero):
    objective = "score result" if element == "Float" else "toFloat (score result)"
    driver = _driver(f"""
        inductive Numbers
        | nil: {{xs:Numbers | Numbers.length xs = 0}}
        | cons (head:{{v:{element} | {zero} <= v && v <= {upper}}}) (tail:Numbers):
            {{xs:Numbers | Numbers.length xs = 1 + Numbers.length tail}}
        + length (xs:Numbers):Int
        def score (xs:Numbers):{element} :=
            match xs with | nil => {zero} | cons h t => h + score t;
        @maximize({objective})
        def result: {{xs:Numbers | 3 = Numbers.length xs}} := ?numbers;
        def main (u:Int):{element} := score result;
    """)
    driver.synth()
    assert driver.run() == 3 * float(upper)


def test_unused_list_refinement_uses_validated_fallback(monkeypatch):
    fallback = CPSatHoleSynthesizer._runtime_search
    calls = []

    def runtime(self, *args, **kwargs):
        calls.append(True)
        return fallback(self, *args, **kwargs)

    monkeypatch.setattr(CPSatHoleSynthesizer, "_runtime_search", runtime)
    driver = _driver(
        MASK
        + """
        def result: {m:Mask{|fun w => fun rest => w + rest <= 6|} |
            Mask.count m = 1 && Mask.weight m = 3} := ?solution;
        @maximize(0.0)
        def unrelated:Int := 0;
        def main (u:Int):Int := score result;
    """
    )
    driver.synth()
    assert driver.run() == 1
    assert calls


def test_empty_list_without_objective():
    driver = _driver("""
        import List;
        def main (u:Int):{xs:(List Bool) | List.size xs = 0} := ?xs;
    """)
    driver.synth()
    assert driver.run() == ("List_nil",)


def test_non_unit_measure_step_is_not_a_length():
    driver = _driver("""
        inductive Steps
        | nil: {xs:Steps | Steps.count xs = 0}
        | cons (h:Bool) (tail:Steps): {xs:Steps | Steps.count xs = Steps.count tail + 2}
        + count (xs:Steps):Int
        def result: {xs:Steps | Steps.count xs = 2} := ?xs;
    """)
    with pytest.raises(UnsupportedSynthesisGoal, match="zero / tail"):
        _solve(driver)


def test_tail_refinement_can_depend_on_the_head(symbolic):
    driver = _driver("""
        inductive Mask
        | empty: {m:Mask | Mask.count m = 0 && Mask.weight m = 0}
        | cons (used:Bool) (rest:{m:Mask | Mask.weight m + (if used then 1 else 0) <= 1}):
            {m:Mask | Mask.count m = Mask.count rest + 1 &&
                Mask.weight m = Mask.weight rest + (if used then 1 else 0)}
        + count (m:Mask):Int
        + weight (m:Mask):Int
        def score (m:Mask):Int :=
            match m with | empty => 0 | cons used rest => (if used then 1 else 0) + score rest;
        @maximize(toFloat (score result))
        def result: {m:Mask | Mask.count m = 3} := ?solution;
        def main (u:Int):Int := score result;
    """)
    driver.synth()
    assert driver.run() == 1
