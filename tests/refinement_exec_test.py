"""Tests for compile-time refinement predicate execution."""

from __future__ import annotations

from aeon.compilation.compile import clear_unit_cache
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import RefinedType
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.lowering import type_to_core
from aeon.sugar.ast_helpers import st_top
from aeon.sugar.parser import parse_expression, parse_type
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.verification.refinement_exec import (
    execute_refinements_in_sterm,
    execute_refinements_in_stype,
    sterm_free_vars,
)
from aeon.backend.evaluator import HoleEvaluationError
import pytest


def _parse_ok(src: str):
    clear_unit_cache()
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=False)
    d = AeonDriver(cfg)
    return list(d.parse(aeon_code=src, filename="<t>"))


def _run(src: str) -> object:
    assert _parse_ok(src) == []
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=False)
    d = AeonDriver(cfg)
    d.parse(aeon_code=src, filename="<t>")
    return d.run()


def test_parse_with_hole_does_not_block_when_stdin_is_not_tty():
    """LSP and other piped invocations must not hang on ``input()`` for holes."""
    import subprocess
    import sys
    import textwrap

    src = textwrap.dedent(
        """\
        @example(double 3 = 6)
        def double (n:Int) : {x:Int | x = 2 * n} :=
            ?h
        """
    )
    script = textwrap.dedent(
        f"""\
        from aeon.facade.driver import AeonConfig, AeonDriver
        from aeon.synthesis.uis.api import SilentSynthesisUI
        src = {src!r}
        cfg = AeonConfig(synthesizer='gp', synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=False)
        d = AeonDriver(cfg)
        errors = list(d.parse(filename='file:///t.ae', aeon_code=src))
        print('errors', len(errors))
        """
    )
    proc = subprocess.run(
        [sys.executable, "-c", script],
        input="",
        capture_output=True,
        text=True,
        timeout=15,
        cwd=__import__("pathlib").Path(__file__).resolve().parents[1],
    )
    assert proc.returncode == 0, proc.stderr
    assert "errors 0" in proc.stdout


def test_parse_minimize_with_hole_skips_refinement_exec_and_does_not_prompt():
    """Main programs with synthesis holes defer compile-time refinement execution."""
    import sys
    import unittest.mock as mock

    src = """@minimize_int(cases_to_order)
def cases_to_order : {c:Int | c > 0 && c * 12 >= 25} := ?hole
"""
    with mock.patch.object(sys.stdin, "isatty", return_value=True):
        assert _parse_ok(src) == []


def test_execute_refinements_raises_on_hole_program():
    src = """@minimize_int(cases_to_order)
def cases_to_order : {c:Int | c > 0 && c * 12 >= 25} := ?hole
"""
    from aeon.sugar.bind import bind_program
    from aeon.sugar.desugar import desugar
    from aeon.sugar.parser import parse_main_program

    prog = bind_program(parse_main_program(src, "<t>"), [])
    desugared = desugar(prog, is_main_hole=False)
    with pytest.raises(HoleEvaluationError):
        execute_refinements_in_sterm(desugared.program, [])


def test_sterm_free_vars_ignores_binder():
    ref = parse_expression("1 + 2 > 0")
    assert sterm_free_vars(ref) == set()


def test_constant_arithmetic_refinement_executes():
    src = "def main (u:Int) : Int := let a : {a:Int | 1 + 2 > 0} := 0 in a;"
    assert _run(src) == 0


def test_constant_arithmetic_refinement_lowers_to_true():
    clear_unit_cache()
    ty = parse_type("{a:Int | 1 + 2 > 0}")
    executed = execute_refinements_in_stype(ty, st_top, [])
    core = type_to_core(executed)
    assert isinstance(core, RefinedType)
    assert core.refinement == LiquidLiteralBool(True)


def test_list_all_refinement_executes_to_true():
    src = """
import List;
def main (u:Int) : Int := let a : {a:Int | List.all (fun x => x > 0) [1, 2, 3]} := 0 in a;
"""
    assert _run(src) == 0


def test_list_all_refinement_lowers_to_true():
    clear_unit_cache()
    from aeon.compilation.compile import compile_imports_for_desugar, _file_imports
    from aeon.sugar.parser import parse_main_program
    from aeon.sugar.desugar import desugar
    from aeon.sugar.bind import bind_program
    from aeon.elaboration import elaborate_collecting_errors

    src = """
import List;
def main (u:Int) : Int := let a : {a:Int | List.all (fun x => x > 0) [1, 2, 3]} := 0 in a;
"""
    prog = parse_main_program(src, filename="<t>")
    prog = bind_program(prog, [])
    dep_units = compile_imports_for_desugar(_file_imports(prog))
    dep_list = list(dep_units.values())
    desugared = desugar(prog, is_main_hole=True, compiled_imports=dep_units)
    sterm, _ = elaborate_collecting_errors(desugared.elabcontext, desugared.program, st_top)
    executed = execute_refinements_in_sterm(sterm, dep_list)

    from aeon.sugar.program import SAbstraction, SLet, SRec
    from aeon.sugar.stypes import SRefinedType

    def find_refined(t):
        if isinstance(t, SRec) and isinstance(t.var_type, SRefinedType):
            return t.var_type
        if isinstance(t, SRec):
            return find_refined(t.var_value) or find_refined(t.body)
        if isinstance(t, SAbstraction):
            return find_refined(t.body)
        if isinstance(t, SLet):
            return find_refined(t.var_value) or find_refined(t.body)
        return None

    refined = find_refined(executed)
    assert refined is not None
    core = type_to_core(refined)
    assert isinstance(core, RefinedType)
    assert core.refinement == LiquidLiteralBool(True)


def test_refinement_partial_subexpr_with_binder():
    clear_unit_cache()
    ty = parse_type("{a:Int | a > 1 + 2}")
    executed = execute_refinements_in_stype(ty, st_top, [])
    core = type_to_core(executed)
    assert isinstance(core, RefinedType)
    assert not isinstance(core.refinement, LiquidLiteralBool)
    from aeon.core.liquid import LiquidApp, LiquidLiteralInt

    ref = core.refinement
    assert isinstance(ref, LiquidApp)
    assert isinstance(ref.args[1], LiquidLiteralInt)
    assert ref.args[1].value == 3


def test_refinement_equality_partial_subexpr():
    clear_unit_cache()
    ty = parse_type("{a:Int | a = 1 + 2}")
    executed = execute_refinements_in_stype(ty, st_top, [])
    core = type_to_core(executed)
    assert isinstance(core, RefinedType)
    from aeon.core.liquid import LiquidApp, LiquidLiteralInt

    ref = core.refinement
    assert isinstance(ref, LiquidApp)
    assert isinstance(ref.args[1], LiquidLiteralInt)
    assert ref.args[1].value == 3


def test_refinement_true_eq_closed_subexpr():
    clear_unit_cache()
    from aeon.compilation.compile import compile_imports_for_desugar, _file_imports
    from aeon.sugar.parser import parse_main_program
    from aeon.sugar.desugar import desugar
    from aeon.sugar.bind import bind_program
    from aeon.elaboration import elaborate_collecting_errors

    src = """
import List;
def main (u:Int) : Int := let a : {a:Int | true = List.all (fun x => x > 0) [1, 2, 3]} := 0 in a;
"""
    prog = parse_main_program(src, filename="<t>")
    prog = bind_program(prog, [])
    dep_units = compile_imports_for_desugar(_file_imports(prog))
    dep_list = list(dep_units.values())
    desugared = desugar(prog, is_main_hole=True, compiled_imports=dep_units)
    sterm, _ = elaborate_collecting_errors(desugared.elabcontext, desugared.program, st_top)
    executed = execute_refinements_in_sterm(sterm, dep_list)

    from aeon.sugar.program import SAbstraction, SLet, SRec
    from aeon.sugar.stypes import SRefinedType

    def find_refined(t):
        if isinstance(t, SRec) and isinstance(t.var_type, SRefinedType):
            return t.var_type
        if isinstance(t, SRec):
            return find_refined(t.var_value) or find_refined(t.body)
        if isinstance(t, SAbstraction):
            return find_refined(t.body)
        if isinstance(t, SLet):
            return find_refined(t.var_value) or find_refined(t.body)
        return None

    refined = find_refined(executed)
    core = type_to_core(refined)
    assert core.refinement == LiquidLiteralBool(True)


def test_refinement_mentioning_binder_not_fully_executed():
    clear_unit_cache()
    ty = parse_type("{a:Int | a > 0}")
    executed = execute_refinements_in_stype(ty, st_top, [])
    core = type_to_core(executed)
    assert isinstance(core, RefinedType)
    assert not isinstance(core.refinement, LiquidLiteralBool)


def test_false_constant_refinement_parses():
    src = "def main (u:Int) : Int := let a : {a:Int | 1 > 2} := 0 in a;"
    assert _parse_ok(src) == []
