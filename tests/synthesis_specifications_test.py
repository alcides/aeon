"""Specifications must survive adaptation to satisfaction-only backends."""

import pytest

from aeon.core.terms import Literal
from aeon.core.types import t_float, t_int
from aeon.synthesis.api import ProgramSynthesizer, Synthesizer, SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from tests.driver import check_and_return_core


def solve(source, backend, budget=2):
    core, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, core)
    return synthesize_holes(ctx, ectx, core, targets, metadata, backend, budget, SilentSynthesisUI())


class FirstValid(Synthesizer):
    supports_optimization = False

    def __init__(self, ty=t_int):
        self.ty = ty
        self.checked = []

    def computations(self, primitives):
        return {}  # The adapter must install its own computation.

    def synthesize(self, *, validate, **kwargs):
        for value in (-1, 0, 1):
            candidate = Literal(float(value) if self.ty == t_float else value, self.ty)
            valid = validate(candidate)
            self.checked.append(valid)
            if valid:
                return candidate
        return None


@pytest.mark.parametrize("spec", ["@example(f 0 > 0)", ""])
def test_refinements_and_extra_checks_both_apply(spec):
    backend = FirstValid()
    prop = "" if spec else "@property(5) def p (x:Int) : Bool := f x > 0;"
    result = solve(f"{spec} def f (x:Int) : {{v:Int | v >= 0}} := ?h; {prop}", backend)
    assert list(result.values()) == [Literal(1, t_int)]
    assert backend.checked == [False, False, True]


@pytest.mark.parametrize("file", [False, True])
def test_both_csv_decorators_become_exact_fit_checks(file, tmp_path):
    csv = tmp_path / "examples.csv"
    csv.write_text("0.0,1.0\n1.0,1.0\n")
    decorator = f'@csv_file("{csv}")' if file else r'@csv_data("0.0,1.0\n1.0,1.0")'
    backend = FirstValid(t_float)
    result = solve(f"{decorator} def f (x:Float) : Float := ?h;", backend)
    assert list(result.values()) == [Literal(1.0, t_float)]
    assert backend.checked == [False, False, True]


def test_conflicting_csv_rows_have_no_exact_fit():
    result = solve(r'@csv_data("0.0,0.0\n0.0,1.0") def f (x:Float) : Float := ?h;', FirstValid(t_float))
    assert list(result.values()) == [None]


@pytest.mark.parametrize("backend", ["backward_lit"])
@pytest.mark.parametrize("objective", ["minimize_int", "maximize_int"])
def test_satisfaction_backends_reject_arbitrary_optimization(backend, objective):
    with pytest.raises(UnsupportedSynthesisGoal, match="cannot optimize"):
        solve(f"@{objective}(f 0) def f (x:Int) : Int := ?h;", make_synthesizer(backend))


@pytest.mark.parametrize("backend", ["fta", "afta", "cata", "lta", "rl_mcts"])
def test_real_refinement_backends_use_general_example_assertions(backend):
    result = solve("@example(f 0 > 0) def f (x:Int) : Int := ?h;", make_synthesizer(backend), budget=4)
    assert all(candidate is not None for candidate in result.values())


@pytest.mark.parametrize("backend", ["contata", "bustle_baseline"])
def test_pbe_backends_accept_additional_property_checks(backend):
    result = solve(
        """
        @example(f 0 = 1)
        @example(f 1 = 1)
        def f (x:Int) : Int := ?h;
        @property(5) def p (x:Int) : Bool := f x = 1;
    """,
        make_synthesizer(backend),
    )
    assert all(candidate is not None for candidate in result.values())


class UncheckedProgram(ProgramSynthesizer):
    def synthesize_program(self, ctx, ectx, term, targets, metadata, budget, ui):
        return {hole: Literal(0, t_int) for _, holes in targets for hole in holes}


def test_program_backends_cannot_skip_properties():
    result = solve("def f (x:Int) : Int := ?h; @property(3) def p (x:Int) : Bool := f x > 0;", UncheckedProgram())
    assert list(result.values()) == [None]


def test_property_relevance_follows_helper_calls():
    backend = FirstValid()
    result = solve(
        """
        def f (x:Int) : Int := ?h;
        def helper (x:Int) : Int := f x;
        @property(3) def p (x:Int) : Bool := helper x > 0;
    """,
        backend,
    )
    assert list(result.values()) == [Literal(1, t_int)]


def test_malformed_relevant_property_is_not_silently_skipped():
    with pytest.raises(UnsupportedSynthesisGoal, match="return type must be Bool"):
        solve("def f (x:Int) : Int := ?h; @property(3) def p (x:Int) : Int := f x;", FirstValid())


def test_no_generated_property_inputs_is_not_success(monkeypatch):
    monkeypatch.setattr("aeon.synthesis.pbt.runner._generate_property_cases", lambda *args: [])
    with pytest.raises(UnsupportedSynthesisGoal, match="no input cases"):
        solve("def f (x:Int) : Int := ?h; @property(3) def p (x:Int) : Bool := f x > 0;", FirstValid())


def test_non_joint_backend_cannot_ignore_relational_property():
    with pytest.raises(UnsupportedSynthesisGoal, match="multiple open holes"):
        solve(
            """def f (x:Int) : Int := ?a; def g (x:Int) : Int := ?b;
            @property(3) def p (x:Int) : Bool := f x = g x;""",
            FirstValid(),
        )


@pytest.mark.parametrize("backend", ["smt", "sygus"])
def test_joint_solvers_enumerate_models_for_optimization(backend):
    implementation = make_synthesizer(backend)
    result = solve(
        """def f (x:Int) : {v:Int | v >= 0 && v <= 1} := ?a;
        @minimize_int(f 0 + g 0)
        @maximize_int(f 0 + g 0)
        def g (x:Int) : {v:Int | v >= 0 && v <= 1} := ?b;""",
        implementation,
        budget=4,
    )
    assert all(term is not None for term in result.values())
    assert len(implementation.pareto_front) >= 2


def test_csv_rows_are_available_to_pbe_backends():
    result = solve(r'@csv_data("1.0,1.0\n2.0,2.0") def f (x:Float) : Float := ?h;', make_synthesizer("afta"))
    assert all(candidate is not None for candidate in result.values())


def test_afta_pbe_search_does_not_bypass_validation(monkeypatch):
    checked = []

    def reject(candidate):
        checked.append(candidate)
        return False

    monkeypatch.setattr("aeon.synthesis.entrypoint.make_validator", lambda *args: reject)
    with pytest.raises(SynthesisNotSuccessful, match="no program consistent"):
        solve("@example(f 0 = 0) def f (x:Int) : Int := ?h;", make_synthesizer("afta"), budget=0.1)
    assert checked


def test_decision_tree_keeps_approximate_csv_regression():
    result = solve(r'@csv_data("0.0,0.0\n0.0,1.0") def f (x:Float) : Float := ?h;', make_synthesizer("decision_tree"))
    assert list(result.values()) == [Literal(0.5, t_float)]


@pytest.mark.parametrize("decorator", ["minimize", "maximize", "minimize_float", "maximize_float"])
def test_signed_difference_is_not_an_example(decorator):
    *_, metadata = check_and_return_core(f"@{decorator}(f 1.0 - 7.0) def f (x:Float) : Float := ?h;")
    assert not any(entry.get("training_data") for entry in metadata.values())


def test_arbitrary_objectives_do_not_stop_at_zero(monkeypatch):
    from aeon.synthesis.modules.decision_tree import DecisionTreeSynthesizer
    from aeon.synthesis.modules.decision_tree import __name__ as module

    seen = []

    def tree_to_term(tree, *args):
        seen.append(tree.max_depth)
        return Literal(float(tree.max_depth - 1), t_float)

    monkeypatch.setattr(f"{module}._tree_to_term", tree_to_term)
    result = solve(
        r"""@csv_data("0.0,0.0\n1.0,1.0")
        @maximize_float(f 0.0)
        def f (x:Float) : Float := ?h;""",
        DecisionTreeSynthesizer(),
    )
    assert seen == [1, 2]
    assert list(result.values()) == [Literal(1.0, t_float)]


@pytest.mark.parametrize("minimize", [True, False])
def test_metric_repair_continues_past_zero_for_arbitrary_objectives(monkeypatch, minimize):
    from aeon.synthesis.decorators import Goal
    from aeon.synthesis.modules.symetric import SymetricSynthesizer
    from aeon.typechecking.context import TypingContext
    from aeon.utils.name import Name

    backend = SymetricSynthesizer(beam=1)
    zero, one = Literal(0, t_int), Literal(1, t_int)
    monkeypatch.setattr(backend, "_collect", lambda *args: ({}, {}))
    monkeypatch.setattr(backend, "_require_suitable", lambda *args: None)
    monkeypatch.setattr(backend, "_neighbors", lambda term, *args: [one] if term == zero else [])

    def construct(goal, has_goals, consider, *args):
        consider(zero)
        return {goal: [zero]}

    monkeypatch.setattr(backend, "_bottom_up", construct)
    function = Name("f", 0)
    result = backend.synthesize(
        TypingContext(),
        t_int,
        lambda _: True,
        lambda term: [float(-term.value if minimize else term.value)],
        function,
        {function: {"goals": [Goal(minimize, 1, function)]}},
        budget=1,
        ui=SilentSynthesisUI(),
    )
    assert result == one
