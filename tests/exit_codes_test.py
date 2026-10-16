"""The CLI must exit non-zero whenever it reports an error, with a distinct
exit code per error category (see ``aeon.facade.exit_codes``).

Regression context: ``main()`` used to print the errors returned by
``driver.parse`` and fall through to an implicit ``exit 0``, so CI treated
broken programs as passing.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from aeon.facade.api import (
    CoreSubtypingError,
    ModuleNotFoundAeonError as AeonImportError,
    InstanceResolutionError,
    LinearUnusedError,
    MethodResolutionError,
    NonOrderableComparisonError,
    UnificationFailedError,
    UnificationKindError,
    UnificationSubtypingError,
    UnificationUnknownTypeError,
)
from aeon.facade.exit_codes import ExitCode, error_exit_code
from aeon.__main__ import synthesis_requested

REPO_ROOT = Path(__file__).resolve().parent.parent


# --- Unit: error class -> exit code mapping ---------------------------------


def _make(cls):
    """Errors are dataclasses; field contents are irrelevant to the mapping."""
    return cls.__new__(cls)


@pytest.mark.parametrize(
    "cls,expected",
    [
        (AeonImportError, ExitCode.IMPORT_ERROR),
        (UnificationSubtypingError, ExitCode.TYPE_MISMATCH),
        (UnificationFailedError, ExitCode.UNIFICATION_ERROR),
        (UnificationKindError, ExitCode.KIND_MISMATCH),
        (UnificationUnknownTypeError, ExitCode.UNKNOWN_NAME),
        (MethodResolutionError, ExitCode.METHOD_RESOLUTION_ERROR),
        (InstanceResolutionError, ExitCode.MISSING_INSTANCE),
        (NonOrderableComparisonError, ExitCode.NON_ORDERABLE_COMPARISON),
        # LinearityError specialises CoreTypeCheckingError and must win.
        (LinearUnusedError, ExitCode.LINEARITY_ERROR),
        (CoreSubtypingError, ExitCode.CORE_TYPE_ERROR),
    ],
)
def test_error_exit_code_mapping(cls, expected):
    assert error_exit_code(_make(cls)) == expected


# --- End to end: the CLI process exit status ---------------------------------


def run_aeon(tmp_path: Path, source: str, *, synthesis: bool = True) -> subprocess.CompletedProcess:
    f = tmp_path / "prog.ae"
    f.write_text(source)
    cmd = [sys.executable, "-m", "aeon", "--no-main", str(f)]
    if synthesis:
        cmd.extend(["--budget", "1"])
    return subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )


def test_synthesis_requested_detects_flags():
    assert synthesis_requested(["file.ae", "-s", "gp"])
    assert synthesis_requested(["file.ae", "--synthesizer", "gp"])
    assert synthesis_requested(["file.ae", "--budget", "10"])
    assert synthesis_requested(["file.ae", "--budget=10"])
    assert not synthesis_requested(["file.ae", "--no-main"])
    assert not synthesis_requested(["file.ae"])


def test_cli_success_exits_zero(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print 42;\n", synthesis=False)
    assert r.returncode == ExitCode.SUCCESS, r.stderr


def test_cli_synthesis_requested_no_holes(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print 42;\n")
    assert r.returncode == ExitCode.SYNTHESIS_NOT_SUCCESSFUL
    assert "No holes to synthesize." in r.stderr


def test_cli_unknown_synthesizer(tmp_path):
    f = tmp_path / "prog.ae"
    f.write_text("def main (x:Int) : Unit := print 42;\n")
    r = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "not_a_real_synthesizer", str(f)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )
    assert r.returncode == ExitCode.OTHER_ERROR
    assert "Unknown synthesizer: not_a_real_synthesizer" in r.stderr


def test_cli_syntax_error(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print (1 +;\n")
    assert r.returncode == ExitCode.SYNTAX_ERROR
    assert "Syntax error" in r.stdout


def test_cli_import_error(tmp_path):
    r = run_aeon(tmp_path, "import NoSuchModule;\ndef main (x:Int) : Unit := print 1;\n")
    assert r.returncode == ExitCode.IMPORT_ERROR


def test_cli_type_mismatch(tmp_path):
    r = run_aeon(tmp_path, 'def main (x:Int) : Unit := y : Int := "hello";\n    print y;\n')
    assert r.returncode == ExitCode.TYPE_MISMATCH
    # The error report must still be printed.
    assert "Type mismatch" in r.stdout


def test_cli_unknown_variable(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print missing_var;\n")
    assert r.returncode == ExitCode.UNKNOWN_NAME


def test_cli_unknown_qualified_name(tmp_path):
    r = run_aeon(tmp_path, 'import String;\ndef main (x:Int) : Unit := print (String.nope "a");\n')
    assert r.returncode == ExitCode.UNKNOWN_NAME


def test_cli_method_resolution_error(tmp_path):
    r = run_aeon(tmp_path, "def main (x:Int) : Unit := print (1.nonexistent);\n")
    assert r.returncode == ExitCode.METHOD_RESOLUTION_ERROR


def test_cli_invalid_refinement(tmp_path):
    src = (
        'import String;\ndef f (s : {x:String | x.len > 0}) : String := s;\ndef main (x:Int) : Unit := print (f "a");\n'
    )
    r = run_aeon(tmp_path, src)
    assert r.returncode == ExitCode.INVALID_REFINEMENT


@pytest.mark.parametrize("result", ["none", "partial", "open"])
def test_cli_unfinished_synthesis_exits_two(tmp_path, monkeypatch, capsys, result):
    import aeon.__main__ as cli
    import aeon.facade.driver as driver_module
    from aeon.core.terms import Hole, Literal
    from aeon.core.types import t_int
    from aeon.utils.name import Name

    def unfinished(ctx, ectx, core, targets, *args, **kwargs):
        names = [hole for _, holes in targets for hole in holes]
        if result == "none":
            return {name: None for name in names}
        if result == "partial":
            return {names[0]: Literal(0, t_int)}
        return {name: Hole(Name("still_open", 987)) for name in names}

    path = tmp_path / "incomplete.ae"
    path.write_text("def x:Int := ?hx; def y:Int := ?hy;")
    monkeypatch.setattr(driver_module, "synthesize_holes", unfinished)
    monkeypatch.setattr(sys, "argv", ["aeon", "--no-main", "-s", "random_search", "--budget", "1", str(path)])
    with pytest.raises(SystemExit) as exc:
        cli.main()
    assert exc.value.code == ExitCode.SYNTHESIS_NOT_SUCCESSFUL
    captured = capsys.readouterr()
    assert "complete solution" in captured.err
    assert "Synthesized holes:" not in captured.out


@pytest.mark.parametrize("exception", [TimeoutError, "evaluation"])
def test_cli_escaping_timeout_exits_two(tmp_path, monkeypatch, capsys, exception):
    import aeon.__main__ as cli
    import aeon.facade.driver as driver_module
    from aeon.synthesis.api import TimeoutInEvaluationException

    def timed_out(*args, **kwargs):
        raise TimeoutInEvaluationException() if exception == "evaluation" else exception()

    path = tmp_path / "timeout.ae"
    path.write_text("def x:Int := ?hx;")
    monkeypatch.setattr(driver_module, "synthesize_holes", timed_out)
    monkeypatch.setattr(sys, "argv", ["aeon", "--no-main", "-s", "random_search", "--budget", "1", str(path)])
    with pytest.raises(SystemExit) as exc:
        cli.main()
    assert exc.value.code == ExitCode.SYNTHESIS_NOT_SUCCESSFUL
    assert "within 1 seconds" in capsys.readouterr().err


def test_complete_synthesis_still_exits_zero(tmp_path):
    path = tmp_path / "complete.ae"
    path.write_text("def x:{v:Int | v = 7} := ?hx;")
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "smt", "--budget", "2", str(path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == ExitCode.SUCCESS, result.stderr
    assert "Synthesized holes:" in result.stdout


def test_cli_backend_without_candidate_exits_two(tmp_path):
    path = tmp_path / "no_candidate.ae"
    path.write_text("def f(x:Int):Int := ?hole;")
    result = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "decision_tree", "--budget", "1", str(path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == ExitCode.SYNTHESIS_NOT_SUCCESSFUL, result.stderr
    assert "unfilled holes" in result.stderr
    assert "Synthesized holes:" not in result.stdout
