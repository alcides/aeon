"""Isolation and lifecycle contracts for compiler sessions."""

import pytest
import asyncio

from aeon.compilation.compile import CompilationState, compile_program
from aeon.compilation.session import CompilationOptions, CompilationSession, current_session
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.verification.constructor_registry import get_constructor_order, register_constructors
from aeon.verification.smt import smt_valid, clear_smt_caches
from aeon.verification.state import VerificationState
from aeon.verification.vcs import LiquidConstraint
from aeon.core.liquid import LiquidLiteralBool


def test_nested_session_restores_owner_even_on_exception():
    outer, inner = CompilationSession(), CompilationSession()
    with outer.activate():
        register_constructors("Private", ["Private_mk"])
        with pytest.raises(RuntimeError), inner.activate():
            assert get_constructor_order("Private") is None
            register_constructors("Inner", ["Inner_mk"])
            raise RuntimeError("abort")
        assert current_session() is outer
        assert get_constructor_order("Private") == ["Private_mk"]
        assert get_constructor_order("Inner") is None


def test_solvers_and_validity_caches_are_session_owned():
    first, second = CompilationSession(), CompilationSession(CompilationOptions(smt_timeout_ms=500))
    with first.activate():
        assert smt_valid(LiquidConstraint(LiquidLiteralBool(True)))
        state = first.state(VerificationState)
        assert state.validity
        solver = state.get_solver()
    with second.activate():
        other = second.state(VerificationState)
        assert not other.validity
        assert other.get_solver() is not solver
        clear_smt_caches()
    assert state.validity


def test_lazy_state_uses_its_owner_configuration_outside_activation():
    session = CompilationSession(CompilationOptions(smt_timeout_ms=750))
    assert session.state(VerificationState).timeout_ms == 750


def test_name_resolution_imports_remain_compatible():
    from aeon.sugar import desugar, name_resolution

    assert desugar.resolve_qualified_names_in_stype is name_resolution.resolve_qualified_names_in_stype


def test_explicit_session_reuses_units_but_independent_sessions_do_not(tmp_path):
    path = str(tmp_path / "Unit.ae")
    source = "def value : Int := 7;"
    first, second = CompilationSession(), CompilationSession()
    with first.activate():
        unit, errors = compile_program(source, filename=path, write_cache=False)
        assert not errors
        cached, errors = compile_program(source, filename=path, write_cache=False)
        assert not errors
        assert cached is unit
    with second.activate():
        assert not second.state(CompilationState).sources
        independent, errors = compile_program(source, filename=path, write_cache=False)
        assert not errors
        assert independent is not unit


def test_driver_reparse_discards_old_state_and_records_diagnostics():
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
    assert not list(driver.parse(aeon_code="def main (u:Int) : Int := 7;", filename="<stdin>"))
    session = driver.session
    assert driver.run() == 7
    errors = list(driver.parse(aeon_code="def main (u:Int) : Int := true;", filename="<stdin>"))
    assert errors
    assert driver.session is not session
    assert driver.session.diagnostics == errors


@pytest.mark.parametrize("options", [{"smt_timeout_ms": 0}, {"cache_limit": -1}])
def test_invalid_session_options_are_rejected(options):
    with pytest.raises(ValueError):
        CompilationOptions(**options)


def test_validity_cache_is_bounded():
    from aeon.core.liquid import LiquidApp, LiquidLiteralInt
    from aeon.utils.name import Name

    session = CompilationSession(CompilationOptions(cache_limit=3))
    with session.activate():
        for value in range(12):
            assert smt_valid(LiquidConstraint(LiquidApp(Name("==", 0), [LiquidLiteralInt(value)] * 2)))
        assert len(session.state(VerificationState).validity) <= 3


def test_interleaved_tasks_keep_their_own_registry():
    async def worker(name):
        with CompilationSession().activate():
            register_constructors("SharedName", [name])
            await asyncio.sleep(0)
            return get_constructor_order("SharedName")

    async def check():
        assert await asyncio.gather(worker("first"), worker("second")) == [["first"], ["second"]]

    asyncio.run(check())
