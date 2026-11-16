"""Complete-candidate deduplication preserves typing distinctions and retries."""

from dataclasses import replace
from time import monotonic_ns, sleep
from unittest.mock import Mock

import pytest
from hypothesis import given, settings, strategies as st

from aeon.compilation.session import CompilationSession, current_session
from aeon.core.terms import Annotation, Literal
from aeon.core.types import TypeConstructor, t_bool, t_float, t_int, top
from aeon.synthesis.evaluation_pool import ERROR, INVALID, OK, TIMEOUT, EvaluationPool, inconclusive_evaluations
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
from aeon.synthesis.modules.tdsyn.worklist import PartialAST
from aeon.synthesis.specifications import checked_validator
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name
from aeon.verification.state import VerificationState


@pytest.fixture(autouse=True)
def session():
    with CompilationSession().activate():
        token = inconclusive_evaluations.set(0)
        yield
        inconclusive_evaluations.reset(token)


def assess(backend, term, validate, evaluate=None, front=None, ui=None):
    backend._has_goals = True
    backend._minimize = [False]
    return backend._try_complete(
        PartialAST(term, [], 0),
        validate,
        evaluate or (lambda _: [1.0]),
        monotonic_ns(),
        ui or SilentSynthesisUI(),
        front or [],
    )


def test_candidate_deduplication_is_opt_in():
    assert not TDSynSynthesizer().deduplicate
    assert TDSynSynthesizer(deduplicate=True).deduplicate


@pytest.mark.parametrize("valid", [True, False])
@pytest.mark.parametrize("deduplicate", [True, False])
def test_complete_assessments_are_not_repeated(valid, deduplicate):
    backend = TDSynSynthesizer(deduplicate=deduplicate)
    validate, evaluate, ui = Mock(return_value=valid), Mock(return_value=[1.0]), Mock()
    term = Literal(1, t_int)
    front, _ = assess(backend, term, validate, evaluate, ui=ui)
    repeated, early = assess(backend, term, validate, evaluate, front, ui)
    assert repeated == front and early is None
    expected = 1 if deduplicate else 2
    assert validate.call_count == ui.register.call_count == expected
    assert evaluate.call_count == (expected if valid else 0)
    assert backend.duplicates_skipped == int(deduplicate)


@settings(max_examples=20, deadline=None)
@given(st.integers(-100, 100))
def test_type_annotations_are_not_erased_by_deduplication(value):
    backend = TDSynSynthesizer(deduplicate=True)
    ctx = built_std_context()
    validate = Mock(side_effect=lambda term: check_type(ctx, term, top))
    valid = Annotation(Literal(value, t_int), t_int)
    invalid = Annotation(Literal(value, t_int), t_bool)
    assert valid == invalid
    for term in (valid, invalid, valid, invalid):
        assess(backend, term, validate)
    assert validate.call_count == 2 and backend.duplicates_skipped == 2


def test_snapshots_preserve_mutable_payloads_native_kinds_and_float_bits():
    backend, validate = TDSynSynthesizer(deduplicate=True), Mock(return_value=True)
    values = [False]
    literal = Literal(values, TypeConstructor(Name("Array", 0), [t_bool]))
    assess(backend, literal, validate)
    values[0] = 0
    assess(backend, literal, validate)
    for value in (0.0, -0.0, 0.0, -0.0):
        assess(backend, Literal(value, t_float), validate)
    assert validate.call_count == 4 and backend.duplicates_skipped == 2


def test_locations_do_not_prevent_deduplication():
    backend, validate = TDSynSynthesizer(deduplicate=True), Mock(return_value=True)
    term = Literal(1, t_int)
    assess(backend, term, validate)
    assess(backend, replace(term, loc=SynthesizedLocation("elsewhere")), validate)
    assert validate.call_count == backend.duplicates_skipped == 1


def test_opaque_payloads_bypass_deduplication():
    backend, validate = TDSynSynthesizer(deduplicate=True), Mock(return_value=True)
    term = Literal(object(), t_int)
    for _ in range(2):
        assess(backend, term, validate)
    assert validate.call_count == backend.dedup_bypassed == 2


@pytest.mark.parametrize("stage", ["validate", "evaluate"])
def test_exceptions_can_be_retried(stage):
    backend = TDSynSynthesizer(deduplicate=True)
    validate, evaluate = Mock(return_value=True), Mock(return_value=[1.0])
    callback = validate if stage == "validate" else evaluate
    callback.side_effect = [RuntimeError("transient failure"), callback.return_value]
    for _ in range(3):
        assess(backend, Literal(1, t_int), validate, evaluate)
    assert callback.call_count == 2 and backend.duplicates_skipped == 1


def test_inconclusive_smt_rejections_can_be_retried():
    backend = TDSynSynthesizer(deduplicate=True)
    state = current_session().state(VerificationState)

    def uncertain(_):
        state.inconclusive_queries += 1
        return False

    validate = Mock(side_effect=uncertain)
    for _ in range(2):
        assess(backend, Literal(1, t_int), validate)
    validate.side_effect = None
    validate.return_value = False
    for _ in range(2):
        assess(backend, Literal(1, t_int), validate)
    assert validate.call_count == 3 and backend.duplicates_skipped == 1


@pytest.mark.parametrize("status", [TIMEOUT, ERROR, INVALID, OK])
def test_worker_status_survives_boolean_validator_wrappers(status):
    def compute(_):
        if status == TIMEOUT:
            sleep(100)
        if status == ERROR:
            raise RuntimeError("worker error")
        if status == INVALID:
            from aeon.synthesis.api import InvalidIndividualException

            raise InvalidIndividualException("invalid candidate")
        return [1]  # A definitive, failed runtime requirement.

    backend = TDSynSynthesizer(deduplicate=True)
    validate = Mock(return_value=True)
    pool = EvaluationPool(lambda t: t, {"specification": compute}, budget_eval=0.05)
    try:
        checked = checked_validator(validate, pool)
        for _ in range(2):
            assess(backend, Literal(1, t_int), checked)
    finally:
        pool.close()
    uncertain = status in (TIMEOUT, ERROR)
    assert validate.call_count == (2 if uncertain else 1)
    assert backend.duplicates_skipped == (0 if uncertain else 1)
    assert inconclusive_evaluations.get() == (2 if uncertain else 0)


def test_deduplication_is_bounded_and_uses_recent_entries():
    backend = TDSynSynthesizer(deduplicate=True, dedup_capacity=2)
    validate = Mock(return_value=True)
    for value in (1, 2, 1, 3, 2):
        assess(backend, Literal(value, t_int), validate)
    assert validate.call_count == 4 and backend.duplicates_skipped == 1
    assert len(backend._completed) == 2
    with pytest.raises(ValueError, match="capacity"):
        TDSynSynthesizer(dedup_capacity=0)


def test_deduplication_precedes_qtt_and_constructor_preparation(monkeypatch):
    from aeon.synthesis.modules.tdsyn import synthesizer

    prepare = Mock(side_effect=lambda term: term)
    monkeypatch.setattr(synthesizer, "bind_constructor_arguments", prepare)
    qtt = Mock(return_value=True)
    backend = TDSynSynthesizer(deduplicate=True)
    backend._has_goals, backend._minimize = True, [False]
    partial = PartialAST(Literal(1, t_int), [], 0, check_sketch=qtt)
    for _ in range(2):
        backend._try_complete(partial, lambda _: True, lambda _: [1.0], monotonic_ns(), SilentSynthesisUI(), [])
    assert qtt.call_count == prepare.call_count == backend.duplicates_skipped == 1


@pytest.mark.parametrize("mode", ["enumerative", "random"])
@pytest.mark.parametrize("expansion", ["eager", "lazy"])
def test_reusing_a_synthesizer_does_not_reuse_previous_rejections(monkeypatch, mode, expansion):
    backend = TDSynSynthesizer(mode=mode, expansion=expansion, deduplicate=True)
    rejected, answer = Literal(0, t_int), Literal(1, t_int)

    def search(initial, skip, validate, evaluate, start_time, budget, ui, front):
        for term in (rejected, rejected, answer):
            front, early = backend._try_complete(PartialAST(term, [], 0), validate, evaluate, start_time, ui, front)
            if early is not None:
                return front, early
        pytest.fail("Expected a no-objective solution")

    monkeypatch.setattr(backend, "_enumerative_search" if mode == "enumerative" else "_random_search", search)
    validate = Mock(side_effect=lambda term: term == answer)
    args = (TypingContext(), t_int, validate, lambda _: [], Name("f", 0), {})
    assert backend.synthesize(*args, ui=SilentSynthesisUI()) == answer
    assert validate.call_count == 2 and backend.duplicates_skipped == 1
    validate.side_effect = lambda term: True
    assert backend.synthesize(*args, ui=SilentSynthesisUI()) == rejected
    assert validate.call_count == 3 and backend.duplicates_skipped == 0
