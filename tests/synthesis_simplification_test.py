"""Final synthesis results are simplified in Core, before rendering."""

import dataclasses

import pytest

from aeon.backend.evaluator import EvaluationContext, eval as evaluate
from aeon.core.multiplicity import M1
from aeon.core.parser import parse_term
from aeon.core.terms import Abstraction, Annotation, Application, If, Let, Literal, Rec, Var
from aeon.core.types import AbstractionType, t_bool, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.optimization.normal_form import simplify_boolean_conditionals
from aeon.synthesis.api import ProgramSynthesizer, Synthesizer
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import incomplete_functions_and_holes
from aeon.synthesis.joint import JointCandidate, JointSynthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


@pytest.mark.parametrize(
    "source, expected",
    [
        ("if c then true else false", "c"),
        ("fun c => if c then true else false", "fun c => c"),
        ("let tag = f x in if tag then true else false", "let tag = f x in tag"),
        ("g (if c then true else false)", "g c"),
        ("if c then (if d then true else false) else false", "if c then d else false"),
        ("if c then 1 else 0", "if c then 1 else 0"),
        ("if c then false else true", "if c then false else true"),
        ("if c then true else true", "if c then true else true"),
    ],
)
def test_boolean_simplification(source, expected):
    assert simplify_boolean_conditionals(parse_term(source)) == parse_term(expected)


def test_simplification_keeps_effectful_condition_once():
    calls = []
    condition = Application(Var(Name("probe")), Literal(0, t_int))
    term = If(condition, Literal(True, t_bool), Literal(False, t_bool))

    def probe(_):
        calls.append(1)
        return False

    ctx = EvaluationContext({Name("probe"): probe})
    assert evaluate(simplify_boolean_conditionals(term), ctx) is False
    assert calls == [1]


def test_simplification_preserves_binding_metadata_and_annotations():
    condition = Var(Name("condition"))
    value = If(condition, Literal(True, t_bool), Literal(False, t_bool))
    name = Name("f")
    term = Rec(
        name,
        t_bool,
        Annotation(value, t_bool),
        Let(name, value, value, multiplicity=M1),
        decreasing_by=(Literal(0, t_int),),
        multiplicity=M1,
        mutual_group_id=7,
    )
    expected = dataclasses.replace(
        term,
        var_value=Annotation(condition, t_bool),
        body=dataclasses.replace(term.body, var_value=condition, body=condition),
    )
    result = simplify_boolean_conditionals(term)
    assert result == expected
    assert result.loc is term.loc
    assert result.var_value.type is term.var_value.type


X, TAG = Name("x", 10001), Name("tag", 10002)
RAW = Abstraction(X, Let(TAG, Var(X), If(Var(TAG), Literal(True, t_bool), Literal(False, t_bool))))
SIMPLIFIED = Abstraction(X, Let(TAG, Var(X), Var(TAG)))


class SingleResult(Synthesizer):
    def synthesize(self, *, validate, **kwargs):
        assert validate(RAW)
        return RAW


class JointResult(JointSynthesizer):
    def synthesize_joint(self, holes, validate, *args):
        candidate = JointCandidate(tuple(RAW for _ in holes))
        assert validate(candidate)
        return candidate


class ProgramResult(ProgramSynthesizer):
    def synthesize_program(self, ctx, ectx, term, targets, *args):
        return {hole: RAW for _, holes in targets for hole in holes}


class RecordingUI(SilentSynthesisUI):
    def __init__(self):
        self.completed = []

    def end(self, solution, quality):
        self.completed.append(solution)


@pytest.mark.parametrize("backend", [SingleResult, JointResult, ProgramResult])
def test_synthesis_returns_simplified_core_for_each_dispatch_path(backend):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 1, no_main=True))
    assert not driver.parse(
        aeon_code="""
        def f : (x:Bool) -> Bool := ?first;
        def g : (x:Bool) -> Bool := ?second;
    """
    )
    ui = RecordingUI()
    with driver.session.activate():
        targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            targets,
            driver.metadata,
            backend(),
            1,
            ui,
        )
    assert len(mapping) == 2
    assert all(term == SIMPLIFIED for term in mapping.values())
    for completed in ui.completed:
        values = completed.terms if isinstance(completed, JointCandidate) else (completed,)
        assert all(value == SIMPLIFIED for value in values)
    # The immutable candidate used in search is unchanged.
    assert isinstance(RAW.body.body, If)


def test_driver_substitutes_simplified_core(monkeypatch):
    monkeypatch.setattr("aeon.facade.driver.make_synthesizer", lambda *args, **kwargs: SingleResult())
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 1, no_main=True))
    assert not driver.parse(aeon_code="def f : (x:Bool) -> Bool := ?hole;")
    assert driver.has_synth()
    driver.synth()
    assert driver.core.var_value == SIMPLIFIED
    namespace = {}
    exec(driver.export("f"), namespace)
    assert namespace["f"](True) is True
    assert namespace["f"](False) is False


def test_no_solution_remains_unfilled(monkeypatch):
    monkeypatch.setattr(SingleResult, "synthesize", lambda *args, **kwargs: None)
    from aeon.core.terms import Hole
    from aeon.typechecking.context import TypingContext

    function, hole = Name("f"), Name("hole")
    program = Rec(function, AbstractionType(X, t_bool, t_bool), Hole(hole), Literal(0, t_int))
    mapping = synthesize_holes(
        TypingContext(),
        EvaluationContext(),
        program,
        [(function, [hole])],
        {},
        SingleResult(),
        budget=1,
        ui=SilentSynthesisUI(),
    )
    assert mapping == {hole: None}
