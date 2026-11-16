"""Typing proof reuse must retain annotations, assumptions and SMT uncertainty."""

from dataclasses import replace

import pytest
from hypothesis import given, settings, strategies as st

from aeon.compilation.session import CompilationSession, current_session
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.terms import Annotation, Literal, Rec, Var
from aeon.core.types import RefinedType, TypeConstructor, t_bool, t_int, top
from aeon.synthesis import entrypoint
from aeon.synthesis.typecheck_cache import TypecheckingCache, _typed_key
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name
from aeon.verification.state import VerificationState


@settings(max_examples=20, deadline=None)
@given(st.integers(-100, 100))
def test_cache_preserves_annotations_and_reuses_both_verdicts(value):
    with CompilationSession().activate():
        ctx = built_std_context()
        valid = Annotation(Literal(value, t_int), t_int)
        invalid = Annotation(Literal(value, t_int), t_bool)
        assert valid == invalid  # Ordinary term equality intentionally erases annotations.
        cache = TypecheckingCache()
        calls = []

        def check(term):
            def compute():
                calls.append(term)
                return check_type(ctx, term, top)

            return cache.check(ctx, term, compute)

        assert check(valid)
        assert not check(invalid)
        assert check(replace(valid, loc=SynthesizedLocation("another occurrence")))
        assert not check(invalid)
        assert len(calls) == 2 and cache.hits == 2


def test_context_mutation_and_expected_type_change_invalidate():
    with CompilationSession().activate():
        binder = VariableBinder(Name("x", 900), t_int)
        ctx = built_std_context().with_var(binder.name, binder.type)
        term = Var(binder.name)
        cache = TypecheckingCache()

        def check(expected):
            return cache.check(ctx, term, lambda: check_type(ctx, term, expected), expected)

        assert check(t_int)
        assert not check(t_bool)
        next(
            entry for entry in ctx.entries if isinstance(entry, VariableBinder) and entry.name == binder.name
        ).type = t_bool
        assert not check(t_int)
        assert check(t_bool)
        assert cache.misses == 4


def test_keys_snapshot_mutable_values_and_distinguish_boolean_integer_elements():
    ty = TypeConstructor(Name("Array", 0), [t_bool])
    values = [False]
    literal = Literal(values, ty)
    first = _typed_key(literal)
    values[0] = 0
    assert first != _typed_key(literal)
    ty.args[0] = t_int
    assert _typed_key(literal) != _typed_key(Literal([0], TypeConstructor(Name("Array", 0), [t_bool])))


def test_trusted_definitions_do_not_leak_proofs_to_an_untrusted_context():
    with CompilationSession().activate():
        name = Name("cached_definition", 0)
        ctx = built_std_context()
        ctx.trusted_names = frozenset({name})
        program = Rec(name, t_int, Literal(True, t_bool), Literal(0, t_int))
        cache = TypecheckingCache()
        assert cache.check(ctx, program, lambda: check_type(ctx, program, top))
        ctx.trusted_names = frozenset()
        assert not cache.check(ctx, program, lambda: check_type(ctx, program, top))
        assert cache.misses == 2


def test_nested_type_refinements_and_hash_collisions_are_distinct():
    yes = RefinedType(Name("v", 901), t_int, LiquidLiteralBool(True))
    no = replace(yes, refinement=LiquidLiteralBool(False))
    assert _typed_key(TypeConstructor(Name("Array", 0), [yes])) != _typed_key(TypeConstructor(Name("Array", 0), [no]))
    assert hash(-1) == hash(-2)
    assert _typed_key(Literal(-1, t_int)) != _typed_key(Literal(-2, t_int))


def test_lru_eviction_sessions_and_solver_reset_do_not_reuse_results():
    cache = TypecheckingCache(max_entries=2)
    ctx = TypingContext()
    calls = []

    def check(n):
        return cache.check(ctx, Literal(n, t_int), lambda: calls.append(n) or True)

    with CompilationSession().activate():
        assert check(1) and check(2) and check(1) and check(3) and check(2)
        assert calls == [1, 2, 3, 2]
        current_session().state(VerificationState).generation += 1
        assert check(2)
    with CompilationSession().activate():
        assert check(2)
    assert calls == [1, 2, 3, 2, 2, 2]


def test_unknown_queries_are_not_cached_as_definitive_failures(monkeypatch):
    from aeon.verification import smt
    from aeon.verification.trace import suspend_verification
    from aeon.verification.vcs import LiquidConstraint

    with CompilationSession().activate():

        def unknown(constraint, key):
            smt._smt_status_cache[key] = ("unknown", "timeout")
            return False

        monkeypatch.setattr(smt, "_smt_valid", unknown)
        cache = TypecheckingCache()
        calls = []

        def check():
            calls.append(True)
            # Horn inference deliberately hides exploratory queries from traces.
            with suspend_verification():
                return smt.smt_valid(LiquidConstraint(LiquidLiteralBool(False)))

        for _ in range(2):
            assert not cache.check(TypingContext(), Literal(0, t_int), check)
        assert len(calls) == 2 and cache.inconclusive == 2 and cache.hits == 0


def test_exceptions_and_opaque_native_values_bypass_caching():
    cache = TypecheckingCache()
    calls = []

    def fail():
        calls.append(True)
        raise ValueError("temporary failure")

    for _ in range(2):
        with pytest.raises(ValueError):
            cache.check(TypingContext(), Literal(1, t_int), fail)
    opaque = Literal(object(), t_int)
    for _ in range(2):
        assert cache.check(TypingContext(), opaque, lambda: True)
    assert len(calls) == 2 and cache.bypassed == 2


def test_shared_validator_keeps_different_program_contracts_separate(monkeypatch):
    calls = []
    original = entrypoint.check_type

    def check(*args):
        calls.append(True)
        return original(*args)

    monkeypatch.setattr(entrypoint, "check_type", check)
    with CompilationSession().activate():
        ctx = built_std_context()
        accepted = entrypoint.make_validator(ctx, lambda t: Annotation(t, t_int))
        rejected = entrypoint.make_validator(ctx, lambda t: Annotation(t, t_bool))
        term = Literal(1, t_int)
        assert accepted(term) and accepted(term)
        assert not rejected(term) and not rejected(term)
        assert len(calls) == 2


def test_program_scoring_reuses_typing_but_still_checks_runtime_requirements(monkeypatch):
    from aeon.synthesis import program_specifications
    from tests.program_specifications_test import specifications

    original = program_specifications.check_type
    calls = []

    def check(*args):
        calls.append(True)
        return original(*args)

    monkeypatch.setattr(program_specifications, "check_type", check)
    with specifications("@require(f = 1) @maximize_int(f) def f : Int := ?h;", pooled=False) as specs:
        good = specs.candidate({specs.holes[0]: Literal(1, t_int)})
        bad = specs.candidate({specs.holes[0]: Literal(0, t_int)})
        assert specs.validate(good)
        assert specs.evaluate(good) == [1.0]
        assert not specs.validate(bad)
        assert not specs.validate(bad)
        assert len(calls) == 2
