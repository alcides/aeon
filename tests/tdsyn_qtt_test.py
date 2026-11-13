"""TDSyn respects QTT both inside generated functions and surrounding sketches."""

import pytest

from aeon.backend.evaluator import EvaluationContext
from aeon.core.multiplicity import M0, M1, MOmega
from aeon.core.terms import Abstraction, Annotation, Application, Hole, If, Literal, Var
from aeon.core.types import AbstractionType, t_bool, t_int
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.joint import JointCandidate
from aeon.synthesis.program_specifications import ProgramSpecifications
from aeon.synthesis.entrypoint import make_validator
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynOneStepSynthesizer, TDSynSynthesizer, _peel_abstractions
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, expand_at_hole, fresh_hole
from aeon.synthesis.qtt import QTTValidator
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.linearity import check_linearity
from aeon.utils.name import Name
from tests.tdsyn_relations_test import _driver


def _goal(mult=M1):
    ctx = TypingContext()
    ty = AbstractionType(Name("x", 1), t_int, t_int, multiplicity=mult)
    term, _, _, holes = _peel_abstractions(ty, ctx)
    return PartialAST(term, holes, 0, expected_type=ty, context=ctx)


def _fill(partial, value, children=()):
    return expand_at_hole(partial, partial.holes[0], value, list(children), partial.depth + 1)


@pytest.mark.parametrize("check_types", [True, False])
def test_validator_checks_qtt_even_for_pretyped_candidates(check_types):
    goal = _goal()
    validate = make_validator(goal.context, lambda term: Annotation(term, goal.expected_type), check_types=check_types)
    assert not validate(Abstraction(goal.term.var_name, Literal(0, t_int)))
    assert validate(Abstraction(goal.term.var_name, Var(goal.term.var_name)))


def test_partial_usage_defers_missing_uses_but_rejects_known_overuse():
    goal = _goal()
    assert goal.qtt_feasible()
    assert not _fill(goal, Literal(0, t_int)).qtt_feasible()
    assert _fill(goal, Var(goal.term.var_name)).qtt_feasible()
    # A later hole cannot undo duplication in a known subterm.
    x = Var(goal.term.var_name)
    f = Name("f", 2)
    linear_binary = AbstractionType(
        Name("a", 3), t_int, AbstractionType(Name("b", 4), t_int, t_int, multiplicity=M1), multiplicity=M1
    )
    goal.context = goal.context.with_var(f, linear_binary)
    duplicate = Application(Application(Var(f), x), x)
    unfinished = If(Hole(Name("later", 5)), duplicate, x)
    assert not _fill(goal, unfinished).qtt_feasible()


def test_erased_argument_is_allowed_in_erased_application():
    goal = _goal(M0)
    f = Name("erase", 2)
    goal.context = goal.context.with_var(f, AbstractionType(Name("a", 3), t_int, t_int, multiplicity=M0))
    assert not _fill(goal, Var(goal.term.var_name)).qtt_feasible()
    assert _fill(goal, Application(Var(f), Var(goal.term.var_name))).qtt_feasible()


@pytest.mark.parametrize("mult,valid", [(M1, True), (MOmega, False), (M0, False)])
def test_application_scales_resource_usage(mult, valid):
    goal = _goal()
    f = Name("f", 2)
    goal.context = goal.context.with_var(f, AbstractionType(Name("a", 3), t_int, t_int, multiplicity=mult))
    assert _fill(goal, Application(Var(f), Var(goal.term.var_name))).qtt_feasible() is valid


def test_branches_share_the_resource_instead_of_adding_uses():
    goal = _goal()
    x = Var(goal.term.var_name)
    assert _fill(goal, If(Literal(True, t_bool), x, x)).qtt_feasible()
    assert not _fill(goal, If(Literal(True, t_bool), x, Literal(0, t_int))).qtt_feasible()


@pytest.mark.parametrize("expansion", ["eager", "lazy"])
def test_expansion_prunes_erased_uses_before_validation(expansion):
    goal = _goal(M0)
    search = TDSynSynthesizer(direction="backward", expansion=expansion)
    expand = search._expand_hole if expansion == "eager" else search._iter_expansions
    candidates = list(expand(goal, goal.holes[0], lambda _: False))
    assert candidates
    assert all(p.qtt_feasible() for p in candidates)
    assert not any(isinstance(p.term.body, Var) for p in candidates)


def test_sketch_pruning_accounts_for_uses_outside_hole():
    x, f, arg = Name("x", 1), Name("f", 2), Name("a", 3)
    ctx = TypingContext().with_var(
        f, AbstractionType(arg, t_int, AbstractionType(arg, t_int, t_int, multiplicity=M1), multiplicity=M1)
    )
    ty = AbstractionType(x, t_int, t_int, multiplicity=M1)

    def replace(candidate):
        return Annotation(Abstraction(x, Application(Application(Var(f), Var(x)), candidate)), ty)

    validate = QTTValidator(lambda _: True, replace, ctx)
    assert validate.feasible(Hole(Name("remaining", 4)))
    assert validate(Literal(0, t_int))
    assert not validate(Var(x))


@pytest.mark.parametrize("backend", ["tdsyn_enumerative", "tdsyn_backward", "tdsyn_random"])
def test_synthesis_consumes_linear_parameter(backend):
    driver = _driver("def identity (1 x:Int):Int := ?body; def main (u:Int):Int := identity 7;", backend)
    driver.synth()
    assert not check_linearity(driver.core, driver.typing_ctx)
    assert driver.run() == 7


@pytest.mark.parametrize("backend", ["tdsyn_enumerative", "tdsyn_backward", "tdsyn_random"])
def test_synthesis_does_not_use_erased_parameter(backend):
    driver = _driver("def erase (0 x:Int):Int := ?body; def main (u:Int):Int := erase 7;", backend)
    driver.synth()
    assert not check_linearity(driver.core, driver.typing_ctx)
    assert isinstance(driver.run(), int)


@pytest.mark.parametrize("mode", ["enumerative", "random"])
@pytest.mark.parametrize("expansion", ["eager", "lazy"])
def test_direct_synthesis_keeps_peeled_signature_through_smt_and_restarts(mode, expansion):
    goal = _goal()
    term = TDSynSynthesizer(mode, expansion=expansion).synthesize(
        goal.context,
        goal.expected_type,
        lambda _: True,
        lambda _: [],
        Name("identity", 20),
        {},
        budget=2,
        ui=SilentSynthesisUI(),
    )
    assert isinstance(term, Abstraction)
    assert term.body == Var(term.var_name)


@pytest.mark.parametrize("mode", ["enumerative", "random"])
def test_input_generation_rejects_smt_models_that_drop_linear_parameters(mode):
    goal = _goal()
    terms = list(
        TDSynSynthesizer(mode).iter_input_candidates(
            goal.context,
            goal.expected_type,
            lambda _: False,
            max_depth=2,
            max_expansions=20,
        )
    )
    valid = [term for term in terms if term is not None]
    assert valid
    assert all(not check_linearity(Annotation(term, goal.expected_type), goal.context) for term in valid)


def test_sibling_arguments_cannot_spend_the_same_linear_resource():
    goal = _goal()
    f, a, b = Name("combine", 2), Name("a", 3), Name("b", 4)
    goal.context = goal.context.with_var(
        f,
        AbstractionType(a, t_int, AbstractionType(b, t_int, t_int, multiplicity=M1), multiplicity=M1),
    )
    hole_ctx = goal.holes[0].context.with_var(f, goal.context.type_of(f))
    first, first_hole = fresh_hole(t_int, hole_ctx)
    second, second_hole = fresh_hole(t_int, hole_ctx)
    partial = _fill(goal, Application(Application(Var(f), first), second), [first_hole, second_hole])
    assert partial.qtt_feasible()
    partial = _fill(partial, Var(goal.term.var_name))
    assert partial.qtt_feasible()  # The second argument may still use no resource.
    assert not _fill(partial, Var(goal.term.var_name)).qtt_feasible()
    assert _fill(partial, Literal(0, t_int)).qtt_feasible()


@pytest.mark.parametrize("action,mult", [("backward_lit", M1), ("backward_close", M0)])
def test_one_step_tactics_reject_invalid_qtt_even_with_permissive_validator(action, mult):
    goal = _goal(mult)
    with pytest.raises(SynthesisNotSuccessful):
        TDSynOneStepSynthesizer(action).synthesize(
            goal.context,
            goal.expected_type,
            lambda _: True,
            lambda _: [],
            Name("target", 20),
            {},
            ui=SilentSynthesisUI(),
        )


def test_complete_program_specifications_enforce_qtt():
    goal = _goal()
    specs = ProgramSpecifications(
        goal.context,
        EvaluationContext({}),
        Annotation(goal.term, goal.expected_type),
        [(Name("target", 20), [goal.holes[0].name])],
        {},
        pooled=False,
    )
    assert not specs.validate(JointCandidate((Literal(0, t_int),)))
    assert specs.validate(JointCandidate((Var(goal.term.var_name),)))
