"""Differential tests: completion witnesses go through Aeon's real compiler."""

from time import monotonic

import pytest
from hypothesis import given, settings, strategies as st

from aeon.compilation.session import CompilationSession
from aeon.core.multiplicity import M1
from aeon.core.terms import Application, Var
from aeon.core.types import AbstractionType, TypeConstructor, t_bool, t_float, t_int, t_string, t_unit
from aeon.elaboration.context import build_typing_context
from aeon.prelude.prelude import typing_vars
from aeon.sugar.lowering import lower_to_core_context
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.modules.type_constrained.prefix import Limits, PrefixEngine, State, Status
from aeon.synthesis.modules.type_constrained.types import Scope
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


def context():
    return lower_to_core_context(build_typing_context(typing_vars)).with_var(
        Name("f", 42001), AbstractionType(Name("arg", 42002), t_int, t_bool)
    )


def checked(engine, prefix, *, accepting=None):
    result = engine.completion_status(State(prefix))
    assert result.status is Status.LIVE, (prefix, result)
    assert result.witness.startswith(prefix)
    term = engine.scope.compile(result.witness)
    assert check_type(engine.scope.ctx, term, engine.scope.expected.core()), (prefix, result.witness, term)
    if accepting is not None:
        assert result.accepting is accepting, (prefix, result)
    return result


@pytest.mark.parametrize(
    "prefix,accepting",
    [
        ("", False),
        ("f", False),
        ("f ", False),
        ("f 0", True),
        ("(f ", False),
        ("1", False),
        ("1 + 2", False),
        ("1 + 2 > 0", True),
        ("if f 0 then ", False),
        ("if f 0 then true else ", False),
        ("let x := 1 in x > ", False),
        ("let x := 1 in x > 0", True),
        ("  \n f 0  ", True),
    ],
)
def test_completion_viability(prefix, accepting):
    checked(PrefixEngine(Scope(context(), t_bool)), prefix, accepting=accepting)


@pytest.mark.parametrize(
    "prefix", ["f true ", "f (false) ", "if 1 then ", "notInScope ", "true + ", "?hole", "native ", "\u00a0true"]
)
def test_invalid_committed_prefix(prefix):
    engine = PrefixEngine(Scope(context(), t_bool))
    assert engine.completion_status(State(prefix)).status is not Status.LIVE


@pytest.mark.parametrize("prefix", ['"', '"hello', '"hi\\', '"hi\\n', '"\\u', '"\\u03', '"λ', '"hello"'])
def test_string_and_escape_prefixes(prefix):
    checked(PrefixEngine(Scope(context(), t_string)), prefix, accepting=prefix == '"hello"')


@pytest.mark.parametrize("prefix", ["1.", "1.e", "1.2e-", ".", "-", "-1.5", "1e", "1e+"])
def test_float_prefixes(prefix):
    checked(PrefixEngine(Scope(context(), t_float)), prefix)


def test_overflowing_float_and_unspellable_qualified_names_are_excluded():
    engine = PrefixEngine(Scope(context().with_var(Name("true.field", 823), t_float), t_float))
    assert engine.completion_status(State("1e99999")).status is not Status.LIVE
    assert "true.field" not in engine.scope.bindings


def test_keyword_prefix_can_be_an_identifier_and_shadowing_keeps_ids():
    ctx = context().with_var(Name("falsehood", 42003), t_int).with_var(Name("x", 42004), t_string)
    ctx = ctx.with_var(Name("x", 42005), t_int)
    engine = PrefixEngine(Scope(ctx, t_int))
    checked(engine, "fals")
    assert engine.scope.compile("x") == Var(Name("x", 42005))
    checked(engine, 'let x := "hello" in 1', accepting=True)
    assert engine.completion_status(State('let x := "hello" in x + ')).status is not Status.LIVE


def test_expected_arrow_and_local_scope():
    ty = AbstractionType(Name("n", 42006), t_int, t_bool)
    engine = PrefixEngine(Scope(context(), ty))
    for prefix in ["fun ", "fun x => ", "fun x => x ", "fun x => x > 0", "fun f => f > 0"]:
        checked(engine, prefix)


def test_qualified_name_and_real_binding_identity():
    ctx = context().with_var(Name("Module.test", 42007), AbstractionType(Name("a", 42008), t_int, t_bool))
    engine = PrefixEngine(Scope(ctx, t_bool))
    checked(engine, "Module.te")
    term = engine.scope.compile("Module.test 0")
    assert isinstance(term, Application) and term.fun == Var(Name("Module.test", 42007))


def test_bounds_deadline_and_no_unknown_cache_poisoning():
    engine = PrefixEngine(Scope(context(), t_bool), Limits(max_states=1))
    assert engine.completion_status(State("f ")).status is Status.UNKNOWN
    engine = PrefixEngine(Scope(context(), t_bool), Limits(cache_size=2))
    assert engine.completion_status(State("f "), monotonic() - 1).status is Status.UNKNOWN
    checked(engine, "f ")
    for prefix in ("true", "false", "f 0"):
        checked(engine, prefix)
    assert len(engine._cache) == 2


def test_uninhabited_supported_and_unsupported_types():
    engine = PrefixEngine(Scope(TypingContext(), t_unit))
    assert engine.completion_status(State()).status is Status.DEAD
    with pytest.raises(UnsupportedSynthesisGoal):
        Scope(context(), TypeConstructor(Name("Tree", 912)))
    with pytest.raises(UnsupportedSynthesisGoal):
        Scope(context(), AbstractionType(Name("x", 91), t_int, t_int, multiplicity=M1))


def test_higher_order_inhabitation_uses_extended_environment():
    identity = AbstractionType(Name("x", 880), t_unit, t_unit)
    ftype = AbstractionType(Name("fn", 881), identity, t_unit)
    engine = PrefixEngine(Scope(TypingContext().with_var(Name("consume", 882), ftype), t_unit))
    checked(engine, "")
    checked(engine, "consume (")
    assert engine._inhabit_cache


def test_session_isolation_and_persistent_snapshots():
    with CompilationSession().activate():
        first = PrefixEngine(Scope(TypingContext().with_var(Name("value", 810), t_bool), t_bool))
        checked(first, "value", accepting=True)
    with CompilationSession().activate():
        second = PrefixEngine(Scope(TypingContext().with_var(Name("value", 811), t_int), t_bool))
        assert second.completion_status(State("value ")).status is Status.DEAD
        assert first.scope.compile("value") == Var(Name("value", 810))
    original = State("f ")
    assert first.advance(original, "0").text == "f 0"
    assert original.text == "f "


@settings(max_examples=30, deadline=None)
@given(st.integers(min_value=0, max_value=99), st.integers(min_value=0, max_value=99), st.sampled_from(["+", "-", "*"]))
def test_finite_grammar_differential_witnesses(a, b, op):
    source = f"{a} {op} {b} > 0"
    engine = PrefixEngine(Scope(context(), t_bool))
    # Search may conservatively run out of resources, but every LIVE answer is
    # independently compiled/checked, including prefixes with the wrong type.
    for end in range(len(source) + 1):
        prefix = source[:end]
        result = engine.completion_status(State(prefix))
        if result.status is Status.LIVE:
            checked(engine, prefix)
    checked(engine, source, accepting=True)
